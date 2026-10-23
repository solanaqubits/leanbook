import copy
import multiprocessing as mp
import os
from pathlib import Path
import signal
import sqlite3
import tempfile
import time
import unittest
from tools.challenge_store.store import Store,Controller,StoreError,normalize,tag
from tools.challenge_store.fixtures import fixture
from tools.challenge_store.conformance import check_history
from tools.challenge_store.bridge import Bridge,loads


def racer(path,q,tx,gate,out,mode='commit'):
    cap=Controller()
    try:
        with Store(path,controller=cap,timeout=15) as s:
            gate.wait(30); start=time.monotonic_ns()
            r=s.abort_pending(q['key'],tx,cap) if mode=='abort' else s.commit_checked(tx,q)
            out.put((start,time.monotonic_ns(),mode,tx,r))
    except BaseException as e: out.put(('error',str(e)))

def crash_worker(path,q,tx,phase,pipe):
    with Store(path) as s:
        original=s._apply
        def hooked(old,new):
            original(old,new)
            if phase=='before':
                pipe.send('ready'); time.sleep(120)
        s._apply=hooked
        s.commit_checked(tx,q)
        pipe.send('ready'); time.sleep(120)

@unittest.skipUnless(os.environ.get('PROVENANCE_STORE_LIVE_TESTS') == '1', 'Enable Lean/SQLite execution explicitly')
class ChallengeStoreTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        b=Bridge()
        try: cls.cfg,cls.q=fixture(b)
        finally:b.close()
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(); self.path=Path(self.tmp.name)/'state.db'
        self.cap=Controller(); Store.initialize(self.path,self.cap)
        self.s=Store(self.path,controller=self.cap)
    def tearDown(self): self.s.close(); self.tmp.cleanup()
    def prepared(self,tx='a',cfg=None,q=None):
        cfg=self.cfg if cfg is None else cfg; q=self.q if q is None else q
        self.s.install_context('v1',cfg,self.cap); self.s.issue(q['key'],self.cap); self.s.register(tx,q)
    def checked_history(self,initial,history):
        final=self.s.inspect()
        result=check_history(self.s.bridge,initial,history,final)
        destination=os.environ.get('CHALLENGE_HISTORY_DIR')
        if destination:
            import json
            p=Path(destination);p.mkdir(parents=True,exist_ok=True)
            with (p/(self._testMethodName+'.json')).open('x') as f:
                json.dump(dict(initial=initial,history=history,final=final,result=result),f,indent=2)
        return result
    def result(self,out):return out['redemption']['result']
    def error(self,code,fn):
        with self.assertRaises(StoreError) as cm:fn()
        self.assertEqual(cm.exception.code,code)
    def test_registration_identity(self):
        self.assertTrue(self.s.register('a',self.q)['administrative']['accepted'])
        self.assertFalse(self.s.register('a',self.q)['administrative']['accepted'])
        q=copy.deepcopy(self.q); q['signed']['manifest']['j']=2
        self.error('transaction_binding_mismatch',lambda:self.s.register('a',q))
        self.assertEqual(len(self.s.inspect()['transactions']),1)
    def test_unissued_can_abort_without_entry(self):
        self.s.register('a',self.q)
        self.assertEqual(self.result(self.s.commit_checked('a',self.q)),{'rejected':{'reason':'challenge_not_issued'}})
        self.assertEqual(self.s.resolve(self.q['key'],'a')['resolution']['result'],'confirmed_not_committed')
    def test_issue_and_reissue(self):
        self.assertFalse(self.s.issue(self.q['key'],self.cap)['administrative']['accepted'])
        self.prepared(); self.assertFalse(self.s.issue(self.q['key'],self.cap)['administrative']['accepted'])
        self.s.commit_checked('a',self.q)
        self.assertFalse(self.s.issue(self.q['key'],self.cap)['administrative']['accepted'])
    def test_new_acceptance_native_signature(self):
        self.prepared(); r=self.result(self.s.commit_checked('a',self.q))
        self.assertEqual(tag(r),'newly_consumed')
        self.assertEqual(r['newly_consumed']['record']['historicalReport']['authorization'],'blocked')
        self.assertEqual(len(self.s.inspect()['accepted']),1)
    def test_signature_denial(self):
        q=copy.deepcopy(self.q); q['signed']['signature'][0]^=1
        self.prepared(q=q)
        self.assertEqual(tag(self.result(self.s.commit_checked('a',q))),'rejected')
        self.assertEqual(self.s.lookup(q['key'])['entry']['value'],'issued')
    def test_context_change_and_immutable_version(self):
        self.prepared(); c=copy.deepcopy(self.cfg); c['expected']['revokedKeys']=[['signer','key']]
        self.s.install_context('v2',c,self.cap)
        self.assertFalse(self.s.install_context('v1',self.cfg,self.cap)['administrative']['accepted'])
        self.assertEqual(self.result(self.s.commit_checked('a',self.q)),{'rejected':{'reason':'context_changed'}})
    def test_all_negative_validation_components(self):
        # Each independent denial uses a separate registered tx/version and challenge.
        mutators=[lambda c:c['expected'].update(expectedSignerId='other'),
          lambda c:c['expected'].update(expectedRoleId='other'),
          lambda c:c['expected'].update(expectedN=99),
          lambda c:c['expected'].update(revokedKeys=[['signer','key']]),
          lambda c:c.update(allowMissingTimestamp=False),
          lambda c:c['limits'].update(maxSnapshotSizeBytes=0),
          lambda c:c['limits'].update(maxProfileSizeBytes=0),
          lambda c:c['limits']['manifest'].update(maxManifestSizeBytes=0),
          lambda c:c['expected']['keyRegistry'][0].update(pubKeyBytes=[0]),
          lambda c:c['limits'].update(maxKeyRegistrySize=0)]
        for i,mut in enumerate(mutators):
            with self.subTest(i=i):
                c=copy.deepcopy(self.cfg); mut(c); v='v'+str(i); q=copy.deepcopy(self.q); q['contextVersion']=v
                self.s.install_context(v,c,self.cap); self.s.issue(q['key'],self.cap); self.s.register(str(i),q)
                self.assertEqual(tag(self.result(self.s.commit_checked(str(i),q))),'rejected')
        self.assertEqual(self.s.inspect()['accepted'],[])
    def test_artifact_denial(self):
        for name in ('snapshot','profile'):
            q=copy.deepcopy(self.q); q[name][0]^=1
            self.s.install_context('v1',self.cfg,self.cap); self.s.issue(q['key'],self.cap); self.s.register(name,q)
            self.assertEqual(tag(self.result(self.s.commit_checked(name,q))),'rejected')
    def test_historical_retry_new_tx_and_revocation(self):
        self.prepared(); first=self.result(self.s.commit_checked('a',self.q))['newly_consumed']['record']
        c=copy.deepcopy(self.cfg); c['expected']['revokedKeys']=[['signer','key']]
        self.s.install_context('v2',c,self.cap)
        for tx in ('a','b'):
            self.s.register(tx,self.q)
            r=self.result(self.s.commit_checked(tx,self.q))
            self.assertEqual(r,{'idempotent_replay_matched':{'record':first}})
        self.assertEqual(self.s.resolve(self.q['key'],'b')['resolution']['result']['confirmed_committed']['kind'],'historicalReturn')
        self.assertEqual(len(self.s.inspect()['accepted']),1)
    def test_bad_retry_preserves_terminal(self):
        self.prepared(); self.s.commit_checked('a',self.q); old=self.s.inspect()
        q=copy.deepcopy(self.q); q['snapshot'][0]^=1
        self.assertEqual(tag(self.result(self.s.commit_checked('a',q))),'rejected')
        self.assertEqual(normalize(self.s.inspect()),normalize(old))
        self.s.register('b',q); self.s.commit_checked('b',q)
        self.assertEqual(tag(dict(self.s.inspect()['transactions'])['b']),'aborted')
    def test_different_statement_already_used(self):
        self.prepared(); self.s.commit_checked('a',self.q)
        q=copy.deepcopy(self.q); q['signed']['manifest']['j']=2
        self.s.register('b',q)
        self.assertEqual(self.result(self.s.commit_checked('b',q)),{'rejected':{'reason':'challenge_already_used'}})
    def test_abort_and_late_commit(self):
        self.prepared(); self.assertEqual(self.s.abort_pending(self.q['key'],'a',self.cap),{'status':'aborted'})
        self.assertEqual(self.result(self.s.commit_checked('a',self.q)),{'rejected':{'reason':'transaction_aborted'}})
        self.assertEqual(self.s.abort_pending(self.q['key'],'a',self.cap)['status'],'already_aborted')
        self.assertEqual(self.s.inspect()['accepted'],[])
    def test_abort_committed_and_absent(self):
        self.assertEqual(self.s.abort_pending(self.q['key'],'missing',self.cap)['status'],'transaction_not_found')
        self.prepared(); self.s.commit_checked('a',self.q)
        self.assertEqual(self.s.abort_pending(self.q['key'],'a',self.cap)['status'],'already_committed')
    def test_resolve_is_read_only_and_binding(self):
        for state in ('absent','pending','committed'):
            if state=='pending':self.prepared()
            if state=='committed':self.s.commit_checked('a',self.q)
            old=self.s.inspect(); self.s.resolve(self.q['key'],'a'); self.assertEqual(self.s.inspect(),old)
        k=copy.deepcopy(self.q['key']); k['challenge']=[9]
        self.error('transaction_binding_mismatch',lambda:self.s.resolve(k,'a'))
    def test_cancel_authority(self):
        self.prepared()
        self.error('access_denied',lambda:self.s.abort_pending(self.q['key'],'a',Controller()))
        self.error('access_denied',lambda:self.s.issue(self.q['key'],None))
        self.assertEqual(tag(dict(self.s.inspect()['transactions'])['a']),'pending')
    def test_schema_constraints_and_final_immutability(self):
        self.prepared(); self.s.commit_checked('a',self.q)
        for sql in ["UPDATE transactions SET tx_state='PENDING'",'DELETE FROM transactions',
                    'DELETE FROM challenge_entries',"UPDATE challenge_entries SET payload_digest=x'00'",
                    "UPDATE context_versions SET config='{}'"]:
            with self.subTest(sql=sql),self.assertRaises(sqlite3.IntegrityError):self.s.db.execute(sql)
    def test_invalid_json_and_missing_schema_rejected(self):
        self.prepared()
        with self.assertRaises(sqlite3.IntegrityError):
            self.s.db.execute("INSERT INTO context_versions VALUES ('bad','a','b','c','not json')")
        self.s.db.execute('DROP TRIGGER tx_update')
        self.error('invalid_storage_state',lambda:self.s.resolve(self.q['key'],'a'))
    def test_lock_timeout_is_not_abort(self):
        self.prepared()
        db=sqlite3.connect(self.path,isolation_level=None); db.execute('BEGIN IMMEDIATE')
        try:
            with Store(self.path,timeout=.02) as s:
                self.error('lock_timeout',lambda:s.commit_checked('a',self.q))
        finally:db.rollback();db.close()
        self.assertEqual(tag(dict(self.s.inspect()['transactions'])['a']),'pending')
    def test_rollback_is_not_terminal_abort(self):
        self.prepared(); old=self.s.inspect(); apply=self.s._apply
        def fail_after(old,new):apply(old,new);raise RuntimeError('injected before commit')
        self.s._apply=fail_after
        with self.assertRaises(RuntimeError):self.s.commit_checked('a',self.q)
        self.s._apply=apply
        self.assertEqual(normalize(self.s.inspect()),normalize(old))
    def run_race(self,modes):
        ctx=mp.get_context('spawn'); gate=ctx.Event(); out=ctx.Queue()
        procs=[ctx.Process(target=racer,args=(str(self.path),self.q,tx,gate,out,mode)) for mode,tx in modes]
        for p in procs:p.start()
        gate.set(); results=[out.get(timeout=90) for _ in procs]
        for p in procs:p.join(30);self.assertEqual(p.exitcode,0)
        self.assertFalse(any(r[0]=='error' for r in results),results)
        return results
    def test_multiprocess_same_statement(self):
        self.prepared(); self.s.register('b',self.q); self.s.register('c',self.q)
        initial=self.s.inspect()
        results=self.run_race([('commit',t) for t in ['a','b','c']])
        history=[dict(start=r[0],end=r[1],input={'commit':{'tx':r[3],'q':self.q}},output=r[4]) for r in results]
        check=self.checked_history(initial,history)
        self.assertEqual(check['status'],'passed',check)
        self.assertEqual(check_history(self.s.bridge,initial,history,self.s.inspect(),budget=0)['status'],'inconclusive')
        tags=[tag(self.result(r[4])) for r in results]
        self.assertEqual(tags.count('newly_consumed'),1)
        self.assertEqual(tags.count('idempotent_replay_matched'),2)
        self.assertEqual(len(self.s.inspect()['accepted']),1)
    def test_multiprocess_abort_commit(self):
        self.prepared(); initial=self.s.inspect(); results=self.run_race([('commit','a'),('abort','a')])
        history=[]
        for r in results:
            inp={'commit':{'tx':'a','q':self.q}} if r[2]=='commit' else {'abort':{'tx':'a'}}
            out=r[4] if r[2]=='commit' else {'administrative':{'accepted':r[4]['status']=='aborted'}}
            history.append(dict(start=r[0],end=r[1],input=inp,output=out))
        self.assertEqual(self.checked_history(initial,history)['status'],'passed')
        final=tag(dict(self.s.inspect()['transactions'])['a'])
        self.assertIn(final,('committed','aborted'))
        for r in results:
            if r[2]=='abort':self.assertEqual(r[4]['status'],'already_committed' if final=='committed' else 'aborted')
    def crash(self,phase):
        self.prepared(); ctx=mp.get_context('spawn'); parent,child=ctx.Pipe(False)
        p=ctx.Process(target=crash_worker,args=(str(self.path),self.q,'a',phase,child));p.start()
        try:
            self.assertTrue(parent.poll(60));self.assertEqual(parent.recv(),'ready')
            os.kill(p.pid,signal.SIGKILL);p.join(20);self.assertEqual(p.exitcode,-signal.SIGKILL)
        finally:
            if p.is_alive():p.kill();p.join()
            parent.close();child.close()
        with Store(self.path) as recovered:
            image=recovered.inspect()
            self.assertEqual(tag(dict(image['transactions'])['a']),'pending' if phase=='before' else 'committed')
            self.assertEqual(len(image['accepted']),0 if phase=='before' else 1)
            self.assertIn('resolution',recovered.resolve(self.q['key'],'a'))
    def test_sigkill_before_commit(self):self.crash('before')
    def test_sigkill_after_commit_before_response(self):self.crash('after')
    def test_sequence_replay_against_model(self):
        model=dict(entries=[],transactions=[],contexts=[],active=[],accepted=[])
        trace=[{'installContext':{'version':'v1','cfg':self.cfg}}, {'issue':{'key':self.q['key']}},
               {'beginTransaction':{'tx':'a','q':self.q}}, {'commit':{'tx':'a','q':self.q}},
               {'beginTransaction':{'tx':'b','q':self.q}}, {'commit':{'tx':'b','q':self.q}},
               {'resolveTransaction':{'key':self.q['key'],'tx':'a'}}]
        for inp in trace:
            expected=self.s.bridge.call(dict(image=model,input=inp));model=expected['image']
            self.assertEqual(self.s._run(inp),expected['output'])
            self.assertEqual(normalize(self.s.inspect()),normalize(model))

    def test_unknown_commit_outcome_resolves_committed(self):
        self.prepared(); real=self.s.db
        class LostReply:
            def __getattr__(self,name):return getattr(real,name)
            def commit(self):
                real.commit()
                raise sqlite3.OperationalError('simulated lost commit acknowledgement')
        self.s.db=LostReply()
        self.error('indeterminate_transaction_state',lambda:self.s.commit_checked('a',self.q))
        self.s.db=real
        self.assertIn('confirmed_committed',self.s.resolve(self.q['key'],'a')['resolution']['result'])
    def test_read_failure_is_not_not_found(self):
        self.prepared(); real=self.s.db
        class ReadFailure:
            def __getattr__(self,name):return getattr(real,name)
            def execute(self,sql,*args):
                if sql.startswith('SELECT * FROM'):raise sqlite3.OperationalError('simulated I/O failure')
                return real.execute(sql,*args)
        self.s.db=ReadFailure()
        try:self.error('read_failure',lambda:self.s.resolve(self.q['key'],'a'))
        finally:self.s.db=real
    def test_invalid_context_document(self):
        self.s.db.execute("INSERT INTO context_versions VALUES ('bad','c','s','p','{}')")
        self.error('invalid_storage_state',lambda:self.s.resolve(self.q['key'],'a'))
    def test_null_state_fields_rejected(self):
        self.prepared()
        with self.assertRaises(sqlite3.IntegrityError):
            self.s.db.execute("UPDATE transactions SET tx_state='COMMITTED',acceptance_kind=NULL WHERE tx_id='a'")
        self.assertEqual(tag(dict(self.s.inspect()['transactions'])['a']),'pending')
    def test_context_scope_fk(self):
        self.s.install_context('v1',self.cfg,self.cap)
        with self.assertRaises(sqlite3.IntegrityError):
            self.s.db.execute("INSERT INTO active_contexts VALUES ('wrong','session','policy','v1')")
    def test_retired_context_cannot_reactivate(self):
        self.s.install_context('v1',self.cfg,self.cap);self.s.install_context('v2',self.cfg,self.cap)
        with self.assertRaises(sqlite3.IntegrityError):
            self.s.db.execute("UPDATE active_contexts SET version_id='v1'")
    def test_different_concurrent_statements(self):
        self.prepared(); q=copy.deepcopy(self.q);q['signed']['manifest']['j']=2
        self.s.register('b',q); initial=self.s.inspect()
        ctx=mp.get_context('spawn');gate=ctx.Event();out=ctx.Queue()
        ps=[ctx.Process(target=racer,args=(str(self.path),req,tx,gate,out)) for tx,req in [('a',self.q),('b',q)]]
        for p in ps:p.start()
        gate.set();results=[out.get(timeout=90) for _ in ps]
        for p in ps:p.join(30);self.assertEqual(p.exitcode,0)
        self.assertFalse(any(r[0]=='error' for r in results),results)
        history=[dict(start=r[0],end=r[1],input={'commit':{'tx':r[3],'q':self.q if r[3]=='a' else q}},output=r[4]) for r in results]
        self.assertEqual(self.checked_history(initial,history)['status'],'passed')
        self.assertEqual(len(self.s.inspect()['accepted']),1)
    def test_cli_resolve(self):
        import subprocess,sys,json
        self.prepared(); inp=Path(self.tmp.name)/'request.json';inp.write_text(json.dumps({'key':self.q['key'],'txId':'a'}))
        p=subprocess.run([sys.executable,'-m','tools.challenge_store.cli','--db',str(self.path),'resolve','--input',str(inp)],capture_output=True,text=True,timeout=40)
        self.assertEqual(p.returncode,0,p.stdout+p.stderr)
        self.assertEqual(loads(p.stdout)['ok']['resolution']['result'],'still_indeterminate')
    def test_duplicate_json_rejected(self):
        with self.assertRaises(ValueError):loads('{"a":1,"a":2}')
    def test_linearization_checker_rejects_impossible_history(self):
        empty=dict(entries=[],transactions=[],contexts=[],active=[],accepted=[])
        history=[dict(start=0,end=1,input={'abort':{'tx':'absent'}},output={'administrative':{'accepted':True}})]
        self.assertEqual(check_history(self.s.bridge,empty,history,empty)['status'],'failed')

    def test_large_persisted_identifier_rejected_before_materialization(self):
        # Counts every column, not only JSON/blobs: long identifiers are also bounded.
        self.s.db.execute("INSERT INTO context_versions VALUES (?,?,?,?,'{}')",('x'*(3*1024*1024),'c','s','p'))
        self.error('storage_limit_exceeded',lambda:self.s.inspect())
    def test_unqualified_sqlite_profile(self):
        from unittest.mock import patch
        with patch('tools.challenge_store.store.sqlite3.sqlite_version','unqualified'):
            self.error('unqualified_configuration',lambda:Store(self.path))

    def test_native_backend_failure_is_rejected_without_consumption(self):
        from unittest.mock import patch
        import subprocess
        self.prepared(); self.s.bridge.close()
        original=subprocess.Popen
        def wrong_version(command,**kwargs):
            command=list(command);command[-1]='deliberately-wrong-version'
            return original(command,**kwargs)
        with patch('tools.challenge_store.bridge.subprocess.Popen',side_effect=wrong_version):
            self.s.bridge=Bridge()
        self.assertEqual(self.result(self.s.commit_checked('a',self.q)),{'rejected':{'reason':'verification_rejected'}})
        self.assertEqual(self.s.inspect()['accepted'],[])

if __name__=='__main__':unittest.main()

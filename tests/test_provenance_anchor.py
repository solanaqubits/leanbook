"""Finite conformance for external-witness protocol; test server is NOT a trust anchor."""
import copy
import json
from dataclasses import replace, asdict
import multiprocessing as mp
from multiprocessing.managers import BaseManager
import os
from pathlib import Path
import signal
import sqlite3
import tempfile
import threading
import unittest
from unittest.mock import patch
from tools.challenge_store.anchor import (AnchoredStore, AnchorError, Ready, Prepared,
    validate_head, valid_transition, checkpoint_digest, enrollment_checkpoint, MAX_EPOCH)
from tools.challenge_store.store import Store, Controller, StoreError
from tools.challenge_store.files import submit_files, prepare_files, FilePackage, FileInputError
from tests.test_provenance_files import package, expected, key_of, sql_state

ID='independently-configured-store-01'

def record_trace(name, value):
    directory=os.environ.get('ANCHOR_TRACE_DIR')
    if directory:
        dest=Path(directory);dest.mkdir(parents=True,exist_ok=True)
        (dest/(name+'.json')).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')


class TestWitness:
    """Unqualified volatile reference only; deployed external independence is untested."""
    def __init__(self): self.heads={};self.lock=threading.Lock();self.writes=0
    def provision(self,identity,head):
        with self.lock:
            if identity in self.heads:raise ValueError('already provisioned')
            validate_head(head)
            if type(head) is not Ready or head.epoch!=0:raise ValueError('not genesis')
            self.heads[identity]=head
    def read(self,identity):
        with self.lock:return self.heads.get(identity)
    def compare_and_set(self,identity,old,new):
        with self.lock:
            if not valid_transition(old,new):raise ValueError('illegal transition')
            if self.heads.get(identity)!=old:return False
            self.heads[identity]=new;self.writes+=1;return True
    def count(self):
        with self.lock:return self.writes

class WitnessManager(BaseManager):pass
WitnessManager.register('TestWitness',TestWitness)

def worker(path,witness,tx,start,out,phase=None):
    try:
        with AnchoredStore(path,store_id=ID,witness=witness,timeout=10) as s:
            if phase:
                def die(p):
                    if p==phase:os.kill(os.getpid(),signal.SIGKILL)
                s._phase=die
                q=prepare_files(s.bridge,expected()['context'],'v1',package())
                s.commit_checked('crash-tx',q)
            else:
                start.wait(20)
                out.put(submit_files(s,tx,'v1',package()))
    except BaseException as e:
        if out is not None:out.put({'error':getattr(e,'code',type(e).__name__)})

class AnchorProtocolTests(unittest.TestCase):
    def test_transitions_forbid_reset_and_wrong_fencing(self):
        r=Ready(3,'a'*64);p=Prepared(3,'a'*64,'b'*64,'1'*32)
        self.assertTrue(valid_transition(r,p));self.assertTrue(valid_transition(p,Ready(4,'b'*64)))
        for a,b in [(r,Ready(4,'b'*64)),(p,r),(p,Ready(4,'a'*64)),(r,replace(p,epoch=2)),(p,replace(p,token='2'*32))]:
            self.assertFalse(valid_transition(a,b))
    def test_cas_fences_stale_token(self):
        w=TestWitness();r=Ready(0,'a'*64);p=Prepared(0,'a'*64,'b'*64,'1'*32)
        w.provision(ID,r);self.assertTrue(w.compare_and_set(ID,r,p))
        self.assertFalse(w.compare_and_set(ID,replace(p,token='2'*32),Ready(1,'b'*64)))
        self.assertEqual(w.read(ID),p)
    def test_invalid_heads(self):
        for h in [None,{},Ready(True,'a'*64),Ready(-1,'a'*64),Ready(MAX_EPOCH+1,'a'*64),Ready(0,'A'*64),Ready(0,'0'*63),Prepared(0,'a'*64,'b'*64,''),Prepared(MAX_EPOCH,'a'*64,'b'*64,'1'*32)]:
            with self.subTest(head=h),self.assertRaises(AnchorError):validate_head(h)
    def test_checkpoint_map_order_and_coverage(self):
        image=dict(contexts=[['v2',{'a':2}],['v1',{'a':1}]],entries=[['k2','issued'],['k1','issued']],transactions=[['tx',{'a':1}]],active=[['scope','v1']],accepted=['k2','k1'])
        digest=checkpoint_digest(ID,image)
        reordered=copy.deepcopy(image)
        for key in ('contexts','entries','transactions','active'):reordered[key].reverse()
        self.assertEqual(digest,checkpoint_digest(ID,reordered))
        for key in image:
            changed=copy.deepcopy(image);changed[key]=[]
            self.assertNotEqual(digest,checkpoint_digest(ID,changed))
        self.assertNotEqual(digest,checkpoint_digest(ID+'other',image))
        changed=copy.deepcopy(image);changed['accepted'].reverse()
        self.assertNotEqual(digest,checkpoint_digest(ID,changed))
    def test_identity_and_profile_binding(self):
        image=dict(contexts=[],entries=[],transactions=[],active=[],accepted=[])
        for ident in ('','x'*257,None):
            with self.assertRaises(AnchorError):checkpoint_digest(ident,image)
        d=checkpoint_digest(ID,image)
        with patch('tools.challenge_store.anchor.DOMAIN','another-profile'):
            self.assertNotEqual(d,checkpoint_digest(ID,image))
    def test_reference_witness_exclusive_provisioning(self):
        w=TestWitness();w.provision(ID,Ready(0,'a'*64))
        with self.assertRaises(ValueError):w.provision(ID,Ready(0,'b'*64))
        self.assertEqual(w.read(ID),Ready(0,'a'*64))

@unittest.skipUnless(os.environ.get('PROVENANCE_STORE_LIVE_TESTS')=='1','Enable real Lean/SQLite execution')
class AnchoredStoreTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name);self.path=self.root/'registry.db'
        self.cap=Controller();Store.initialize(self.path,self.cap);self.e=expected();self.cfg=self.e['context'];self.key=key_of(self.cfg)
        self.w=TestWitness()
        with Store(self.path,controller=self.cap) as s:
            s.install_context('v1',self.cfg,self.cap);s.issue(self.key,self.cap)
            self.genesis=enrollment_checkpoint(s,ID,self.cap)
        self.w.provision(ID,self.genesis)
        self.s=AnchoredStore(self.path,store_id=ID,witness=self.w,controller=self.cap)
    def tearDown(self):self.s.close();self.temp.cleanup()
    def assert_store_error(self,code,fn):
        with self.assertRaises(StoreError) as e:fn()
        self.assertEqual(e.exception.code,code)
    def request(self):return prepare_files(self.s.bridge,self.cfg,'v1',package())
    def backup(self,dest):
        with sqlite3.connect(dest) as db:self.s.db.backup(db)
    def restore(self,src):
        self.s.close()
        with sqlite3.connect(src) as old,sqlite3.connect(self.path) as current:old.backup(current)
        self.s=AnchoredStore(self.path,store_id=ID,witness=self.w,controller=self.cap)
    def test_full_files_retry_resolve_and_authorization(self):
        out=submit_files(self.s,'first','v1',package())
        self.assertEqual(out['redemption']['result']['newly_consumed']['record'],self.e['record'])
        self.assertEqual(self.w.read(ID).epoch,2)
        before=sql_state(self.s);writes=self.w.count()
        submit_files(self.s,'first','v1',package())
        self.assertEqual(sql_state(self.s),before);self.assertEqual(self.w.count(),writes)
        submit_files(self.s,'second','v1',package());self.assertEqual(self.w.read(ID).epoch,4)
        self.s.close();self.s=AnchoredStore(self.path,store_id=ID,witness=self.w)
        self.assertIn('confirmed_committed',self.s.resolve(self.key,'first')['resolution']['result'])
        self.assertEqual(self.e['record']['historicalReport']['authorization'],'blocked')
    def test_old_database_backup_refused(self):
        old=self.root/'old.db';self.backup(old)
        submit_files(self.s,'first','v1',package());head=self.w.read(ID)
        self.restore(old);before=sql_state(self.s)
        for fn in [self.s.inspect,lambda:self.s.lookup(self.key),lambda:self.s.resolve(self.key,'first'),lambda:submit_files(self.s,'attack','v1',package()),self.s.recover_anchor]:
            self.assert_store_error('anchor_state_mismatch',fn)
        self.assertEqual(sql_state(self.s),before);self.assertEqual(self.w.read(ID),head)
    def test_missing_and_wrong_identity_never_bootstrap(self):
        self.s.store_id='unprovisioned-id';before=sql_state(self.s)
        self.assert_store_error('anchor_not_provisioned',self.s.inspect)
        self.assert_store_error('anchor_not_provisioned',self.s.recover_anchor)
        self.assertEqual(sql_state(self.s),before);self.assertIsNone(self.w.read('unprovisioned-id'))
        self.w.provision('unprovisioned-id',self.genesis)
        self.assert_store_error('anchor_state_mismatch',self.s.inspect)
    def test_unavailable_or_malformed_read_zero_diff(self):
        before=sql_state(self.s);q=self.request()
        for value in (None,{},Ready(True,'a'*64)):
            with patch.object(self.w,'read',return_value=value):
                self.assert_store_error('anchor_not_provisioned' if value is None else 'anchor_invalid_response',lambda:self.s.register('tx',q))
            self.assertEqual(sql_state(self.s),before)
        with patch.object(self.w,'read',side_effect=OSError('offline')):
            self.assert_store_error('anchor_unavailable',lambda:self.s.register('tx',q))
        self.assertEqual(sql_state(self.s),before)
    def test_failed_cas_rolls_back_uncommitted_registration(self):
        before=sql_state(self.s);q=self.request()
        for answer,code in [(False,'anchor_conflict'),(None,'anchor_invalid_response'),(1,'anchor_invalid_response')]:
            with patch.object(self.w,'compare_and_set',return_value=answer):self.assert_store_error(code,lambda:self.s.register('tx',q))
            self.assertEqual(sql_state(self.s),before);self.assertEqual(self.w.read(ID),self.genesis)
    def test_prepare_response_loss_blocks_old_snapshot_recovery(self):
        before=sql_state(self.s);q=self.request();cas=self.w.compare_and_set
        def lost(*args):cas(*args);raise OSError('response lost')
        with patch.object(self.w,'compare_and_set',side_effect=lost):self.assert_store_error('anchor_indeterminate',lambda:self.s.register('tx',q))
        self.assertEqual(sql_state(self.s),before);self.assertIsInstance(self.w.read(ID),Prepared)
        self.assert_store_error('anchor_recovery_required',self.s.inspect)
        self.assert_store_error('anchor_recovery_blocked',self.s.recover_anchor)
    def test_finalize_failure_recovery_changes_no_registry_rows(self):
        q=self.request();cas=self.w.compare_and_set
        def fail_final(identity,old,new):
            if type(new) is Ready:raise OSError('offline')
            return cas(identity,old,new)
        with patch.object(self.w,'compare_and_set',side_effect=fail_final):self.assert_store_error('anchor_indeterminate',lambda:self.s.register('tx',q))
        before=sql_state(self.s);self.assertIsInstance(self.w.read(ID),Prepared)
        self.assert_store_error('anchor_recovery_required',lambda:self.s.resolve(self.key,'tx'))
        self.assertEqual(self.s.recover_anchor(),'anchor_finalized')
        self.assertEqual(sql_state(self.s),before)
        self.assertEqual(self.s.recover_anchor(),'already_current')
        self.assertEqual(self.s.resolve(self.key,'tx')['resolution']['result'],'still_indeterminate')
    def test_finalize_reply_lost_is_not_false_rollback(self):
        q=self.request();cas=self.w.compare_and_set
        def lost_final(identity,old,new):
            answer=cas(identity,old,new)
            if type(new) is Ready:raise OSError('lost final ACK')
            return answer
        with patch.object(self.w,'compare_and_set',side_effect=lost_final):self.assert_store_error('anchor_indeterminate',lambda:self.s.register('tx',q))
        self.assertIsInstance(self.w.read(ID),Ready)
        self.assertEqual(self.s.recover_anchor(),'already_current')
        self.assertEqual(len(self.s.inspect()['transactions']),1)
    def test_recovery_does_not_bless_old_backup_after_local_commit(self):
        old=self.root/'old.db';self.backup(old);q=self.request()
        def fail_phase(p):
            if p=='local_committed':raise OSError('lost process before finalization')
        with patch.object(self.s,'_phase',side_effect=fail_phase),self.assertRaises(OSError):self.s.register('tx',q)
        self.restore(old);self.assert_store_error('anchor_recovery_blocked',self.s.recover_anchor)
        self.assert_store_error('anchor_recovery_required',self.s.inspect)
    def test_read_only_operations_do_not_advance_anchor(self):
        before=sql_state(self.s);head=self.w.read(ID)
        self.s.inspect();self.s.lookup(self.key);self.s.resolve(self.key,'none');self.s.recover_anchor()
        self.assertEqual(sql_state(self.s),before);self.assertEqual(self.w.read(ID),head);self.assertEqual(self.w.count(),0)
    def test_preflight_failure_does_not_touch_anchor(self):
        before=sql_state(self.s);head=self.w.read(ID)
        p=self.root/'bad.bytes';p.write_bytes(b'bad')
        with self.assertRaises(FileInputError):submit_files(self.s,'bad','v1',FilePackage(p,package().signature,package().snapshot,package().profile))
        self.assertEqual(sql_state(self.s),before);self.assertEqual(self.w.read(ID),head)
    def test_crypto_rejection_anchors_aborted_not_consumed(self):
        p=self.root/'sig';p.write_bytes(bytes(64))
        out=submit_files(self.s,'bad','v1',FilePackage(package().manifest,p,package().snapshot,package().profile))
        self.assertIn('rejected',out['redemption']['result']);self.assertEqual(self.w.read(ID).epoch,2)
        self.assertEqual(self.s.inspect()['entries'][0][1],'issued')
        self.assertEqual(self.s.resolve(self.key,'bad')['resolution']['result'],'confirmed_not_committed')
    def test_admin_mutations_and_abort_are_guarded(self):
        q=self.request();self.s.register('tx',q);self.s.abort_pending(self.key,'tx',self.cap)
        self.assertEqual(self.s.resolve(self.key,'tx')['resolution']['result'],'confirmed_not_committed')
        cfg=copy.deepcopy(self.cfg);cfg['expected']['activeChallenge']=[9]
        self.s.install_context('v2',cfg,self.cap);self.s.issue(key_of(cfg),self.cap)
        self.assertEqual(self.w.read(ID).epoch,4)
        self.assertEqual(self.s.recover_anchor(),'already_current')
        with self.assertRaises(StoreError):enrollment_checkpoint(self.s,ID,Controller())
    def test_binding_failure_before_prepare_preserves_anchor(self):
        q=self.request();self.s.register('tx',q);before=sql_state(self.s);head=self.w.read(ID)
        other=copy.deepcopy(q);other['signed']['manifest']['signerId']+='x'
        self.assert_store_error('transaction_binding_mismatch',lambda:self.s.register('tx',other))
        self.assertEqual(sql_state(self.s),before);self.assertEqual(self.w.read(ID),head)
    def test_epoch_exhaustion_rolls_back(self):
        self.w.heads[ID]=Ready(MAX_EPOCH,self.genesis.digest);before=sql_state(self.s)
        self.assert_store_error('anchor_epoch_exhausted',lambda:self.s.register('tx',self.request()))
        self.assertEqual(sql_state(self.s),before)
    def test_sql_commit_failure_before_and_after_durable_write(self):
        for after in (False,True):
            with self.subTest(after_commit=after):
                old=self.root/('backup'+str(after)+'.db');self.backup(old)
                original=self.s.db
                class FaultConnection:
                    def __getattr__(self,name):return getattr(original,name)
                    def commit(self):
                        if after:original.commit()
                        raise sqlite3.OperationalError('injected COMMIT error')
                self.s.db=FaultConnection()
                try:self.assert_store_error('indeterminate_transaction_state',lambda:self.s.register('sql-failure',self.request()))
                finally:self.s.db=original
                if after:
                    self.assertEqual(self.s.recover_anchor(),'anchor_finalized')
                    self.assertEqual(len(self.s.inspect()['transactions']),1)
                else:
                    self.assert_store_error('anchor_recovery_blocked',self.s.recover_anchor)
                    # Separate test reset only, never a production recovery operation.
                    self.restore(old);self.w=TestWitness();self.w.provision(ID,self.genesis);self.s.witness=self.w
    def test_concurrent_finalization_exact_head_is_idempotent(self):
        cas=self.w.compare_and_set
        def other_finishes(identity,old,new):
            answer=cas(identity,old,new)
            return False if type(new) is Ready else answer
        with patch.object(self.w,'compare_and_set',side_effect=other_finishes):self.s.register('tx',self.request())
        self.assertEqual(self.s.recover_anchor(),'already_current')
    def test_stale_witness_counterexample_requires_fresh_external_state(self):
        old=self.root/'old.db';self.backup(old)
        submit_files(self.s,'accepted','v1',package());self.restore(old)
        self.assert_store_error('anchor_state_mismatch',self.s.inspect)
        # Deliberately violating the provider contract defeats detection. A valid
        # historical signature without a fresh read would have the same limitation.
        with patch.object(self.w,'read',return_value=self.genesis):
            self.assertEqual(self.s.inspect()['transactions'],[])
    def test_old_sql_snapshot_against_advanced_witness_refuses_then_refreshes(self):
        q=self.request();old_read=self.w.read;advanced=False
        def advance_during_read(identity):
            nonlocal advanced
            if not advanced:
                advanced=True
                # WAL allows this writer while the first connection holds an old
                # read snapshot. A new witness head must not bless that snapshot.
                with AnchoredStore(self.path,store_id=ID,witness=self.w) as other:
                    other.register('legitimate',q)
            return old_read(identity)
        with patch.object(self.w,'read',side_effect=advance_during_read):
            self.assert_store_error('anchor_state_mismatch',self.s.inspect)
        image=self.s.inspect()
        self.assertEqual([tx for tx,_ in image['transactions']],['legitimate'])
        self.assertEqual(image['accepted'],[])
        self.assertEqual(self.s.recover_anchor(),'already_current')
    def test_sigkill_each_commit_boundary(self):
        ctx=mp.get_context('spawn')
        for phase in ('before_prepare','prepared','local_committed','finalized'):
            with self.subTest(phase=phase):
                # Independent DB and independently provisioned TEST witness per case.
                path=self.root/(phase+'.db')
                Store.initialize(path,self.cap)
                with Store(path,controller=self.cap) as raw:
                    raw.install_context('v1',self.cfg,self.cap);raw.issue(self.key,self.cap)
                    q=prepare_files(raw.bridge,self.cfg,'v1',package());raw.register('crash-tx',q)
                    genesis=enrollment_checkpoint(raw,ID,self.cap)
                with WitnessManager(ctx=ctx) as manager:
                    w=manager.TestWitness();w.provision(ID,genesis)
                    p=ctx.Process(target=worker,args=(path,w,None,None,None,phase));p.start();p.join(45)
                    if p.is_alive():p.kill();p.join();self.fail('worker timeout')
                    self.assertEqual(p.exitcode,-signal.SIGKILL)
                    with AnchoredStore(path,store_id=ID,witness=w) as recovered:
                        if phase=='prepared':
                            self.assert_store_error('anchor_recovery_blocked',recovered.recover_anchor)
                        else:
                            self.assertEqual(recovered.recover_anchor(),'anchor_finalized' if phase=='local_committed' else 'already_current')
                            result=recovered.resolve(self.key,'crash-tx')['resolution']['result']
                            if phase=='before_prepare':self.assertEqual(result,'still_indeterminate')
                            else:self.assertIn('confirmed_committed',result)
                        head=w.read(ID)
                        record_trace('crash-'+phase,dict(phase=phase,exitcode=p.exitcode,head_type=type(head).__name__,head=asdict(head),rows={k:len(v) for k,v in sql_state(recovered).items()}))
    def test_multiprocess_only_one_consumption(self):
        ctx=mp.get_context('spawn')
        with WitnessManager(ctx=ctx) as manager:
            w=manager.TestWitness();w.provision(ID,self.genesis)
            start=ctx.Event();out=ctx.Queue()
            procs=[ctx.Process(target=worker,args=(self.path,w,'parallel'+str(i),start,out)) for i in range(2)]
            for p in procs:p.start()
            start.set();results=[out.get(timeout=60) for _ in procs]
            for p in procs:
                p.join(10)
                if p.is_alive():p.kill();p.join()
                self.assertEqual(p.exitcode,0)
            # A peer may see Prepared, or an old WAL snapshot against a new Ready
            # head, and fail closed. Reopen the read transaction on retry.
            for i,result in enumerate(results):
                if 'error' in result:self.assertIn(result['error'],('anchor_recovery_required','anchor_conflict','anchor_state_mismatch'))
            with AnchoredStore(self.path,store_id=ID,witness=w) as s:
                s.recover_anchor()
                for i in range(2):submit_files(s,'parallel'+str(i),'v1',package())
                image=s.inspect();self.assertEqual(len(image['accepted']),1)
                self.assertEqual(len(image['transactions']),2)
                record_trace('concurrent',dict(results=results,head=asdict(w.read(ID)),accepted_count=len(image['accepted']),transaction_count=len(image['transactions'])))
                self.assertEqual(sum('newly_consumed' in r.get('redemption',{}).get('result',{}) for r in results),1)

if __name__=='__main__':unittest.main()

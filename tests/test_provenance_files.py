"""Fixed disk vectors → real strict Lean decoder → JSON → native crypto → SQLite.
No fixture generation or signing occurs during this test suite.
"""
import copy
import hashlib
import io
import json
import multiprocessing as mp
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
from tools.challenge_store.bridge import Bridge,loads
from tools.challenge_store.store import Store,Controller
from tools.challenge_store.files import FilePackage,FileInputError,read_bounded,_bounded_stream,prepare_files,submit_files

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'tests/data/provenance_files/vectors'
FIELDS=('manifest','signature','snapshot','profile')

def package(name='good'):
    return FilePackage(*(DATA/name/(f+'.bytes') for f in FIELDS))
def expected(name='good'):return loads((DATA/name/'expected.json').read_text())
def key_of(cfg):
    c=cfg['expected'];return dict(scope=dict(contextId=c['contextId'],sessionId=c['expectedSessionId'],policyVersion=c['expectedPolicyVersion']),challenge=c['activeChallenge'])
def sql_state(s):
    return {t:s.db.execute('SELECT * FROM '+t+' ORDER BY 1,2,3,4').fetchall()
            for t in ('context_versions','active_contexts','challenge_entries','transactions')}
def serialized_sql(s):
    return {table:[[{'blob_hex':v.hex()} if isinstance(v,bytes) else v for v in row] for row in rows]
            for table,rows in sql_state(s).items()}
def canonical(x):return json.dumps(x,ensure_ascii=True,sort_keys=True,separators=(',',':'))
def commit_worker(path,gate,out,ready):
    try:
        with Store(path) as s:
            ready.set()
            gate.wait(30)
            out.put(submit_files(s,'legitimate','v1',package()))
    except BaseException as e:out.put({'error':str(e)})

@unittest.skipUnless(os.environ.get('PROVENANCE_STORE_LIVE_TESTS')=='1','Enable Lean/SQLite execution explicitly')
class ProvenanceFileTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        self.cap=Controller();self.path=self.root/'registry.db'
        Store.initialize(self.path,self.cap);self.s=Store(self.path,controller=self.cap)
        self.e=expected();self.cfg=copy.deepcopy(self.e['context'])
    def tearDown(self):self.s.close();self.temp.cleanup()
    def setup_context(self,cfg=None,issued=True):
        c=cfg or self.cfg;self.s.install_context('v1',c,self.cap)
        if issued:self.s.issue(key_of(c),self.cap)
    def failure(self,code,action):
        with self.assertRaises(FileInputError) as e:action()
        self.assertEqual(e.exception.code,code)
    def replacement(self,field,raw):
        p=self.root/(field+'.bytes');p.write_bytes(raw)
        return FilePackage(**{f:p if f==field else getattr(package(),f) for f in FIELDS})
    def assert_sql_result(self,before,cfg,e,tx,state,kind=None,reason=None,new=False):
        after=sql_state(self.s);wanted=copy.deepcopy(before)
        c=cfg['expected'];kt=(c['contextId'],c['expectedSessionId'],c['expectedPolicyVersion'],bytes(c['activeChallenge']))
        if new:
            rec=e['record']
            wanted['challenge_entries']=[(*kt,'CONSUMED',bytes(rec['payloadDigest']),'v1',canonical(rec['historicalReport']))]
        wanted['transactions'].append((tx,*kt,bytes(e['message']),state,kind,reason,1 if new else None))
        wanted['transactions'].sort()
        self.assertEqual(after,wanted)
        golden=loads((DATA/'expected_sql.json').read_text())[tx]
        self.assertEqual(serialized_sql(self.s),golden['after'])
    def test_fixed_vector_integrity(self):
        manifest=loads((DATA/'manifest.json').read_text())
        for f in manifest['files']:
            b=(DATA/f['path']).read_bytes()
            self.assertEqual(len(b),f['size']);self.assertEqual(hashlib.sha256(b).hexdigest(),f['sha256'])
    def test_full_path_reopen_retries_and_exact_sql(self):
        self.setup_context();before=sql_state(self.s)
        self.assertEqual(serialized_sql(self.s),loads((DATA/'expected_sql.json').read_text())['first']['before'])
        out=submit_files(self.s,'first','v1',package())
        self.assertEqual(out,{'redemption':{'result':{'newly_consumed':{'record':self.e['record']}}}})
        self.assert_sql_result(before,self.cfg,self.e,'first','COMMITTED','newAcceptance',new=True)
        self.s.close();self.s=Store(self.path,controller=self.cap)
        r=self.s.resolve(key_of(self.cfg),'first')
        self.assertEqual(r,{'resolution':{'result':{'confirmed_committed':{'record':self.e['record'],'kind':'newAcceptance'}}}})
        before=sql_state(self.s)
        for tx in ('first','second'):
            out=submit_files(self.s,tx,'v1',package())
            self.assertEqual(out,{'redemption':{'result':{'idempotent_replay_matched':{'record':self.e['record']}}}})
            if tx=='first':self.assertEqual(sql_state(self.s),before)
            else:self.assert_sql_result(before,self.cfg,self.e,tx,'COMMITTED','historicalReturn')
    def test_unicode_and_large_values_structural_bridge(self):
        e=expected('unicode');self.setup_context(e['context'])
        q=prepare_files(self.s.bridge,e['context'],'v1',package('unicode'))
        self.assertEqual(q['signed']['manifest'],e['manifest'])
        self.assertEqual(self.s.bridge.call({'binding':q})['message'],e['message'])
        self.assertEqual(submit_files(self.s,'unicode','v1',package('unicode'))['redemption']['result']['newly_consumed']['record'],e['record'])
    def test_fixed_negative_suite_and_exact_sql_diffs(self):
        cases=loads((DATA/'cases.json').read_text())
        for i,case in enumerate(cases):
            with self.subTest(case=case['id']):
                self.s.close();p=self.root/('case'+str(i)+'.db');Store.initialize(p,self.cap);self.s=Store(p,controller=self.cap)
                cfg=copy.deepcopy(self.cfg)
                if 'contextField' in case:cfg['expected'][case['contextField']]+='-mismatch'
                self.setup_context(cfg,case.get('issued',True));before=sql_state(self.s)
                golden=loads((DATA/'expected_sql.json').read_text())[case['id']]
                self.assertEqual(serialized_sql(self.s),golden['before'])
                pkg=package()
                if 'field' in case:pkg=FilePackage(**{f:DATA/case['file'] if f==case['field'] else getattr(pkg,f) for f in FIELDS})
                if case['phase']=='preflight':
                    self.failure(case['error'],lambda:submit_files(self.s,case['id'],'v1',pkg))
                    self.assertEqual(sql_state(self.s),before)
                    self.assertEqual(serialized_sql(self.s),golden['after'])
                else:
                    out=submit_files(self.s,case['id'],'v1',pkg)
                    self.assertEqual(out,{'redemption':{'result':{'rejected':{'reason':case['reason']}}}})
                    self.assert_sql_result(before,cfg,self.e,case['id'],'ABORTED',reason=case['reason'])
    def test_all_four_file_size_limits_zero_diff(self):
        self.setup_context();before=sql_state(self.s)
        for f in FIELDS:
            n=64 if f=='signature' else 4096
            with self.subTest(file=f):
                pkg=self.replacement(f,b'X'*(n+1))
                self.failure('limit_exceeded',lambda:submit_files(self.s,f,'v1',pkg))
                self.assertEqual(sql_state(self.s),before)
    def test_signature_short_zero_diff(self):
        self.setup_context();before=sql_state(self.s)
        for n in (0,1,63):
            self.failure('malformed_signature',lambda:submit_files(self.s,'short','v1',self.replacement('signature',b'X'*n)))
            self.assertEqual(sql_state(self.s),before)
    def test_bad_manifest_short_circuits_remaining_files(self):
        self.setup_context();before=sql_state(self.s)
        pkg=FilePackage(DATA/'manifest-tail/manifest.bytes',self.root/'absent-signature',self.root/'absent-snapshot',self.root/'absent-profile')
        self.failure('decode_rejected',lambda:submit_files(self.s,'early','v1',pkg))
        self.assertEqual(sql_state(self.s),before)
    def test_missing_files_zero_diff(self):
        self.setup_context();before=sql_state(self.s)
        for f in FIELDS:
            pkg=FilePackage(**{n:self.root/'missing' if n==f else getattr(package(),n) for n in FIELDS})
            self.failure('read_failure',lambda:submit_files(self.s,f,'v1',pkg))
            self.assertEqual(sql_state(self.s),before)
    def test_io_failure_before_eof_zero_diff_for_each_file(self):
        self.setup_context();before=sql_state(self.s)
        for index in range(4):
            count=0
            def interrupt(stream,limit):
                nonlocal count
                current=count;count+=1
                if current==index:
                    stream.read(1)
                    raise OSError('injected read interruption before EOF')
                return _bounded_stream(stream,limit)
            with patch('tools.challenge_store.files._bounded_stream',side_effect=interrupt):
                self.failure('read_failure',lambda:submit_files(self.s,'iofail','v1',package()))
            self.assertEqual(sql_state(self.s),before)
    def test_non_regular_inputs_rejected_without_blocking(self):
        self.setup_context();before=sql_state(self.s);fifo=self.root/'fifo';os.mkfifo(fifo)
        descriptors=len(list(Path('/proc/self/fd').iterdir()))
        for path in (fifo,self.root):
            pkg=FilePackage(path,package().signature,package().snapshot,package().profile)
            self.failure('unsupported_file_type',lambda:submit_files(self.s,'bad','v1',pkg))
            self.assertEqual(len(list(Path('/proc/self/fd').iterdir())),descriptors)
            self.assertEqual(sql_state(self.s),before)
    def test_limits_include_context_before_registration(self):
        self.cfg['limits']['maxKeyRegistrySize']=0;self.setup_context();before=sql_state(self.s)
        self.failure('limit_exceeded',lambda:submit_files(self.s,'limits','v1',package()))
        self.assertEqual(sql_state(self.s),before)
    def test_manifest_string_challenge_and_zero_size_limits(self):
        for i,field in enumerate(('maxStringBytes','maxChallengeBytes','maxManifestSizeBytes')):
            cfg=copy.deepcopy(self.cfg);cfg['limits']['manifest'][field]=0
            self.s.install_context('version'+str(i),cfg,self.cap);before=sql_state(self.s)
            self.failure('limit_exceeded' if field=='maxManifestSizeBytes' else 'decode_rejected',lambda:submit_files(self.s,field,'version'+str(i),package()))
            self.assertEqual(sql_state(self.s),before)
    def test_structural_bridge_checks_every_field(self):
        raw=list(package().manifest.read_bytes());m=self.e['manifest'];limits=self.cfg['limits']['manifest']
        for field in m:
            changed=copy.deepcopy(m);v=changed[field]
            if isinstance(v,str):changed[field]=v+'x'
            elif type(v) is int:changed[field]=v+1
            elif field=='epsilon':changed[field]=[1,3]
            elif field=='claimedTime':changed[field]=None
            elif isinstance(v,list):changed[field]=v+[1]
            else:changed[field]['sizeBytes']+=1
            self.assertFalse(self.s.bridge.call({'checkManifestBridge':dict(limits=limits,bytes=raw,manifest=changed)}),field)
    def test_corrupted_bridge_response_zero_diff(self):
        self.setup_context();before=sql_state(self.s);real=self.s.bridge.call
        def corrupt(obj):
            result=real(obj)
            if 'decodeManifest' in obj:result['manifest']['n']+=1
            return result
        with patch.object(self.s.bridge,'call',side_effect=corrupt):
            self.failure('bridge_mismatch',lambda:submit_files(self.s,'badbridge','v1',package()))
        self.assertEqual(sql_state(self.s),before)
    def test_retry_mutated_artifacts_preserves_original(self):
        self.setup_context();submit_files(self.s,'first','v1',package());before=sql_state(self.s)
        for f in ('snapshot','profile'):
            p=FilePackage(**{n:DATA/(f+'-mutated')/(f+'.bytes') if n==f else getattr(package(),n) for n in FIELDS})
            self.assertEqual(submit_files(self.s,'first','v1',p)['redemption']['result'],{'rejected':{'reason':'verification_rejected'}})
            self.assertEqual(sql_state(self.s),before)
    def test_historical_repeat_uses_pinned_context(self):
        self.setup_context();submit_files(self.s,'first','v1',package())
        cfg=copy.deepcopy(self.cfg);cfg['expected']['revokedKeys']=[['fixture-signer','rfc8032-key1']]
        self.s.install_context('v2',cfg,self.cap)
        self.assertIn('idempotent_replay_matched',submit_files(self.s,'second','v1',package())['redemption']['result'])
    def test_unknown_context_zero_diff(self):
        before=sql_state(self.s)
        self.failure('unknown_context_version',lambda:submit_files(self.s,'x','unknown',package()))
        self.assertEqual(sql_state(self.s),before)
    def test_preflight_does_not_register_even_with_other_writer(self):
        self.setup_context();ctx=mp.get_context('spawn');gate=ctx.Event();ready=ctx.Event();out=ctx.Queue()
        proc=ctx.Process(target=commit_worker,args=(str(self.path),gate,out,ready));proc.start()
        try:
            self.assertTrue(ready.wait(60))
            pkg=self.replacement('manifest',package().manifest.read_bytes()+b'\0')
            committed=[]
            def interleave(stream,limit):
                raw=_bounded_stream(stream,limit)
                # Other worker commits while this request is still in its file-read phase.
                gate.set();committed.append(out.get(timeout=60))
                return raw
            with patch('tools.challenge_store.files._bounded_stream',side_effect=interleave):
                self.failure('decode_rejected',lambda:submit_files(self.s,'bad-request','v1',pkg))
            self.assertIn('newly_consumed',committed[0]['redemption']['result'])
            proc.join(20);self.assertEqual(proc.exitcode,0)
            self.assertEqual([r[0] for r in sql_state(self.s)['transactions']],['legitimate'])
        finally:
            if proc.is_alive():proc.kill();proc.join()
    def test_cli_disk_path(self):
        self.setup_context();p=self.root/'input.json';p.write_text('{"txId":"cli-file"}')
        args=[sys.executable,'-m','tools.challenge_store.cli','--db',str(self.path),'submit-files','--context-version','v1','--input',str(p)]
        for f in FIELDS:args+=['--'+f,str(getattr(package(),f))]
        r=subprocess.run(args,cwd=ROOT,capture_output=True,text=True,timeout=60)
        self.assertEqual(r.returncode,0,r.stdout+r.stderr)
        self.assertEqual(loads(r.stdout)['ok']['redemption']['result']['newly_consumed']['record'],self.e['record'])
    def test_no_file_reopen_after_registration(self):
        self.setup_context();pkg=FilePackage(*(self.root/(f+'.bytes') for f in FIELDS))
        for f in FIELDS:getattr(pkg,f).write_bytes(getattr(package(),f).read_bytes())
        real=self.s.register
        def register(tx,q):
            for f in FIELDS:getattr(pkg,f).unlink()
            return real(tx,q)
        with patch.object(self.s,'register',side_effect=register):
            self.assertIn('newly_consumed',submit_files(self.s,'held-bytes','v1',pkg)['redemption']['result'])

class BoundedFileReadTests(unittest.TestCase):
    def test_short_reads_require_eof(self):
        class Short:
            def __init__(self):self.parts=iter([b'a',b'b',b'']);self.requests=[]
            def read(self,n):self.requests.append(n);return next(self.parts)
        s=Short();self.assertEqual(_bounded_stream(s,2),b'ab');self.assertEqual(len(s.requests),3)
    def test_probe_is_one_byte_past_limit(self):
        s=io.BytesIO(b'x'*100)
        with self.assertRaises(FileInputError):_bounded_stream(s,4)
        self.assertEqual(s.tell(),5)
    def test_io_error_before_eof_is_not_success(self):
        class Broken:
            def read(self,n):raise OSError('injected read failure')
        with self.assertRaises(OSError):_bounded_stream(Broken(),64)
    def test_zero_limit_accepts_empty_only(self):
        self.assertEqual(_bounded_stream(io.BytesIO(b''),0),b'')
        with self.assertRaises(FileInputError):_bounded_stream(io.BytesIO(b'x'),0)

if __name__=='__main__':unittest.main()

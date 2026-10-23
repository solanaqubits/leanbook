"""Real subprocess CLI + loopback mTLS + native Lean/SQLite, not provider qualification."""
import copy
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout, redirect_stderr
from unittest.mock import patch

from tools.challenge_store.anchored_cli import main, MAX_ENVELOPE_BYTES
from tools.challenge_store.anchor import Ready, Prepared, enrollment_checkpoint
from tools.challenge_store.store import Store, Controller
from tests.test_witness_https import TLSFixture, ID
from tests.test_witness_config import document, save
from tests.test_provenance_files import package, expected, key_of, sql_state


class ArgumentTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        self.base=['--db',str(self.root/'missing.db'),'--config',str(self.root/'missing.json'),
                   '--config-sha256','0'*64]
    def tearDown(self):self.temp.cleanup()
    def envelope(self,raw):
        p=self.root/'input.json';p.write_bytes(raw);return str(p)
    def refuse(self,args):
        out=io.StringIO()
        with redirect_stdout(out),patch('tools.challenge_store.anchored_cli.AnchoredStore',side_effect=AssertionError('DB forbidden')):
            self.assertEqual(main(self.base+args),2)
        report=json.loads(out.getvalue());self.assertEqual(report['status'],'error')
        self.assertEqual(report['authorization'],'blocked');self.assertFalse(report['external_service_qualified'])
        self.assertNotIn(str(self.root),out.getvalue());self.assertFalse((self.root/'missing.db').exists())
    def test_missing_config_refuses_without_store(self):self.refuse(['inspect'])
    def test_malformed_duplicate_and_extra_fields_precede_config(self):
        for raw in (b'[]',b'null',b'{"txId":"a","txId":"b"}',b'\xff',b'['*2000,
                    b'{"key":{},"txId":"a","report":{"valid":true}}'):
            with self.subTest(raw=raw[:20]):self.refuse(['resolve','--input',self.envelope(raw)])
    def test_identifiers_and_challenge_are_strict(self):
        key=key_of(expected()['context'])
        cases=[dict(key=key,txId=x) for x in ('','x'*257,'\ud800',True)]
        for c in ([True],[-1],[256],['1'],None):
            k=copy.deepcopy(key);k['challenge']=c;cases.append(dict(key=k,txId='a'))
        k=copy.deepcopy(key);k['scope']['extra']='x';cases.append(dict(key=k,txId='a'))
        for obj in cases:
            with self.subTest(obj=repr(obj)[:80]):self.refuse(['resolve','--input',self.envelope(json.dumps(obj).encode())])
    def test_envelope_size_and_fifo_refuse(self):
        self.refuse(['lookup','--input',self.envelope(b'x'*(MAX_ENVELOPE_BYTES+1))])
        fifo=self.root/'fifo';os.mkfifo(fifo)
        self.refuse(['lookup','--input',str(fifo)])
    def test_no_administrative_or_fallback_operations(self):
        for operation in ('init','issue','abort','recover','reset','register','commit'):
            with self.subTest(operation=operation),redirect_stderr(io.StringIO()),self.assertRaises(SystemExit) as e:
                main(self.base+[operation])
            self.assertEqual(e.exception.code,2)
        self.assertFalse((self.root/'missing.db').exists())
    def test_missing_submission_fields_and_irrelevant_flags(self):
        for args in (['submit-files'],['inspect','--input','input.json'],['inspect','--fallback']):
            with self.subTest(args=args),redirect_stderr(io.StringIO()),self.assertRaises(SystemExit) as e:
                main(self.base+args)
            self.assertEqual(e.exception.code,2)


@unittest.skipUnless(os.environ.get('PROVENANCE_STORE_LIVE_TESTS')=='1','live Lean/native bridge')
class AnchoredCLITests(TLSFixture):
    def setUp(self):
        super().setUp();self.cap=Controller();self.db=self.root/'registry.db'
        Store.initialize(self.db,self.cap);self.cfg=expected()['context'];self.key=key_of(self.cfg)
        with Store(self.db,controller=self.cap) as s:
            s.install_context('v1',self.cfg,self.cap);s.issue(self.key,self.cap)
            genesis=enrollment_checkpoint(s,'cli-store',self.cap)
        self.server.allowed.add('cli-store');self.backend.provision('cli-store',genesis)
        for name in ('ca.pem','client.pem','client.key'):
            shutil.copyfile(self.certs/name,self.root/name);(self.root/name).chmod(0o600)
        self.config=document(self.root,port=self.cfg_port(),pin=self.pins['server']);self.config['store_id']='cli-store'
        self.config_path,self.pin=save(self.root,self.config)
    def cfg_port(self):return self.server.server_address[1]
    def state(self):
        with Store(self.db) as s:return sql_state(s)
    def call(self,operation,*,obj=None,files=None,pin=None,db=None):
        cmd=[sys.executable,'-m','tools.challenge_store.anchored_cli','--db',str(db or self.db),
             '--config',str(self.config_path),'--config-sha256',pin or self.pin,operation]
        if obj is not None:
            p=self.root/'request.json';p.write_text(json.dumps(obj));cmd+=['--input',str(p)]
        if operation=='submit-files':
            cmd+=['--context-version','v1'];f=files or package()
            for name in ('manifest','signature','snapshot','profile'):cmd+=['--'+name,str(getattr(f,name))]
        p=subprocess.run(cmd,capture_output=True,text=True,timeout=40)
        self.assertEqual(p.stderr,'',p.stderr);out=json.loads(p.stdout)
        self.assertEqual(out['authorization'],'blocked');self.assertFalse(out['external_service_qualified'])
        self.assertEqual(out['protection'],'anchored')
        return p.returncode,out
    def test_inspect_lookup_and_unknown_resolve_are_read_only(self):
        before=self.state();head=self.backend.read('cli-store')
        for op,obj in [('inspect',None),('lookup',{'key':self.key}),('resolve',{'key':self.key,'txId':'unknown'})]:
            code,out=self.call(op,obj=obj);self.assertEqual(code,0);self.assertEqual(out['status'],'completed')
        self.assertEqual(self.state(),before);self.assertEqual(self.backend.read('cli-store'),head)
        self.assertTrue(self.server.requests);self.assertTrue(all(q['operation']=='read' for q in self.server.requests))
    def test_submission_reopen_resolve_and_same_new_tx_retry(self):
        code,out=self.call('submit-files',obj={'txId':'first'});self.assertEqual(code,0)
        self.assertEqual(out['result']['redemption']['result']['newly_consumed']['record'],expected()['record'])
        before=self.state()
        code,out=self.call('submit-files',obj={'txId':'first'});self.assertEqual(code,0)
        self.assertIn('idempotent_replay_matched',out['result']['redemption']['result']);self.assertEqual(self.state(),before)
        code,out=self.call('submit-files',obj={'txId':'second'});self.assertEqual(code,0)
        after=self.state();self.assertEqual(len(after['transactions']),2);self.assertEqual(len(after['challenge_entries']),1)
        self.assertEqual([r[-3] for r in after['transactions']],['newAcceptance','historicalReturn'])
        code,out=self.call('resolve',obj={'key':self.key,'txId':'first'});self.assertEqual(code,0)
        self.assertIn('confirmed_committed',out['result']['resolution']['result']);self.assertEqual(self.state(),after)
    def test_config_pin_failure_prevents_db_and_network_use(self):
        before=self.state();code,out=self.call('inspect',pin='0'*64)
        self.assertEqual(code,2);self.assertEqual(out['error'],'configuration_pin_mismatch')
        self.assertEqual(self.server.requests,[]);self.assertEqual(self.state(),before)
    def test_missing_db_is_never_initialized(self):
        missing=self.root/'never-created.db';code,out=self.call('inspect',db=missing)
        self.assertEqual(code,2);self.assertEqual(out['error'],'store_not_initialized');self.assertFalse(missing.exists())
        self.assertEqual(self.server.requests,[])
    def test_unavailable_service_never_falls_back(self):
        before=self.state();self.server.status=503
        for op,obj in [('inspect',None),('submit-files',{'txId':'failed'})]:
            code,out=self.call(op,obj=obj);self.assertEqual(code,2);self.assertEqual(out['error'],'anchor_unavailable')
        self.assertEqual(self.state(),before);self.assertTrue(all(q['operation']=='read' for q in self.server.requests))
    def test_missing_or_prepared_anchor_never_enrolls_or_recovers(self):
        before=self.state();self.config['store_id']='absent';self.server.allowed.add('absent')
        self.config_path,self.pin=save(self.root,self.config)
        code,out=self.call('inspect');self.assertEqual(code,2);self.assertEqual(out['error'],'anchor_not_provisioned')
        self.assertIsNone(self.backend.read('absent'))
        self.config['store_id']='cli-store';self.config_path,self.pin=save(self.root,self.config)
        old=self.backend.read('cli-store');head=Prepared(old.epoch,old.digest,'b'*64,'1'*32)
        self.backend.cas('cli-store',old,head)
        code,out=self.call('inspect');self.assertEqual(code,2);self.assertEqual(out['error'],'anchor_recovery_required')
        self.assertEqual(self.backend.read('cli-store'),head);self.assertEqual(self.state(),before)
    def test_mismatched_checkpoint_is_not_accepted_by_probe_semantics(self):
        self.config['store_id']=ID;self.config_path,self.pin=save(self.root,self.config)
        before=self.state();code,out=self.call('inspect')
        self.assertEqual(code,2);self.assertEqual(out['error'],'anchor_state_mismatch');self.assertEqual(self.state(),before)
    def test_bad_file_before_registration_preserves_state(self):
        from dataclasses import replace
        before=self.state();bad=self.root/'bad.bytes';bad.write_bytes(package().manifest.read_bytes()+b'\x00')
        code,out=self.call('submit-files',obj={'txId':'bad-file'},files=replace(package(),manifest=bad))
        self.assertEqual(code,2);self.assertEqual(out['status'],'error');self.assertEqual(self.state(),before)
        self.assertTrue(all(q['operation']=='read' for q in self.server.requests))
    def test_bad_signature_is_completed_rejection_not_successful_acceptance(self):
        from dataclasses import replace
        raw=bytearray(package().signature.read_bytes());raw[0]^=1;bad=self.root/'bad.sig';bad.write_bytes(raw)
        code,out=self.call('submit-files',obj={'txId':'bad-signature'},files=replace(package(),signature=bad))
        self.assertEqual(code,0);self.assertIn('rejected',out['result']['redemption']['result'])
        state=self.state();self.assertEqual(state['transactions'][0][6],'ABORTED');self.assertEqual(state['challenge_entries'][0][4],'ISSUED')
    def test_lost_prepare_response_preserves_uncertainty_and_no_retry(self):
        before=self.state();self.server.mode='lose_cas'
        code,out=self.call('submit-files',obj={'txId':'lost'})
        self.assertEqual(code,2);self.assertEqual(out['error'],'anchor_indeterminate')
        self.assertNotIn('rolled_back',out);self.assertNotIn('ABORTED',json.dumps(out))
        self.assertEqual(self.state(),before);self.assertIsInstance(self.backend.read('cli-store'),Prepared)
        self.assertEqual(sum(q['operation']=='cas' for q in self.server.requests),1)


if __name__=='__main__':unittest.main()

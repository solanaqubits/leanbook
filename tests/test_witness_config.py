"""Pinned deployment input, secret-safe CLI, and real read-only TLS observations."""
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import patch

from tests.test_witness_https import TLSFixture, certificates, ID, SID
from tools.challenge_store.anchor import Ready, Prepared, AnchoredStore, enrollment_checkpoint
from tools.challenge_store.witness_config import (
    DeploymentError, load_deployment, main, probe, MAX_CONFIG_BYTES, MAX_CREDENTIAL_BYTES)
from tools.challenge_store.witness_https import WitnessTransportError


def document(root, *, port=8443, pin='0'*64):
    return dict(schema='witness-deployment/v1', deployment_id='reviewed-service',
                revision='revision-1', store_id=ID, transport=dict(
                    host='localhost', port=port, server_id=SID,
                    ca_file=str(root/'ca.pem'), client_cert=str(root/'client.pem'),
                    client_key=str(root/'client.key'), server_cert_sha256=pin,
                    timeout_seconds=1.0))


def save(root, obj=None, *, raw=None):
    path = root/'deployment.json'
    data = raw if raw is not None else json.dumps(obj, ensure_ascii=True).encode()
    path.write_bytes(data);path.chmod(0o600)
    return path, hashlib.sha256(data).hexdigest()


def load(pair):
    return load_deployment(pair[0], expected_sha256=pair[1])


class ConfigTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cert_temp=tempfile.TemporaryDirectory();cls.certs=Path(cls.cert_temp.name)
        cls.pins=certificates(cls.certs)
    @classmethod
    def tearDownClass(cls):cls.cert_temp.cleanup()
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        for name in ('ca.pem','client.pem','client.key'):
            shutil.copyfile(self.certs/name,self.root/name);(self.root/name).chmod(0o600)
        self.obj=document(self.root,pin=self.pins['server'])
    def tearDown(self):self.temp.cleanup()
    def reject(self, pair, code=None):
        with self.assertRaises((DeploymentError,WitnessTransportError)) as error:load(pair)
        if code:self.assertEqual(error.exception.code,code)
    def test_valid_config_parses_tls_without_network(self):
        with patch('socket.create_connection',side_effect=AssertionError('network forbidden')):
            d=load(save(self.root,self.obj));d.make_witness()
        self.assertEqual((d.store_id,d.revision),(ID,'revision-1'))
        self.assertNotIn(str(self.root/'client.key'),repr(d))
    def test_independent_pin_precedes_tls_construction(self):
        pair=save(self.root,self.obj)
        with patch('tools.challenge_store.witness_config.HTTPSWitness',side_effect=AssertionError('TLS forbidden')):
            self.reject((pair[0],'1'*64),'configuration_pin_mismatch')
            self.reject((pair[0],'invalid'),'invalid_configuration_pin')
    def test_whitespace_and_revision_changes_require_new_pin(self):
        pair=save(self.root,self.obj)
        pair[0].write_bytes(pair[0].read_bytes()+b'\n')
        self.reject(pair,'configuration_pin_mismatch')
        self.obj['revision']='revision-2';new=save(self.root,self.obj)
        self.assertEqual(load(new).revision,'revision-2')
        self.reject((new[0],pair[1]),'configuration_pin_mismatch')
    def test_strict_schema_rejects_duplicates_extra_missing_and_version(self):
        for raw in (b'{}',b'[]',b'{"schema":1,"schema":2}',b'\xff',b'['*2000):
            with self.subTest(raw=raw[:20]):self.reject(save(self.root,raw=raw))
        for name,value in [('schema','v2'),('approved',True),('transport',{})]:
            obj=copy.deepcopy(self.obj);obj[name]=value
            with self.subTest(name=name):self.reject(save(self.root,obj))
    def test_typed_limits_and_no_implicit_transport_defaults(self):
        for name,value in [('port',True),('port',0),('port',65536),('host','https://localhost'),
                           ('timeout_seconds',True),('timeout_seconds',0),('timeout_seconds',31),
                           ('timeout_seconds',float('nan')),('timeout_seconds',10**400),
                           ('server_cert_sha256','A'*64)]:
            obj=copy.deepcopy(self.obj);obj['transport'][name]=value
            with self.subTest(name=name,value=value):self.reject(save(self.root,obj))
        obj=copy.deepcopy(self.obj);del obj['transport']['timeout_seconds']
        self.reject(save(self.root,obj),'invalid_config_schema')
    def test_identity_control_surrogates_and_limits(self):
        for value in ('','x'*257,'bad\nidentity','\ud800'):
            obj=copy.deepcopy(self.obj);obj['store_id']=value
            with self.subTest(value=repr(value)):self.reject(save(self.root,obj))
        obj=copy.deepcopy(self.obj);obj['store_id']='сессия-α'
        self.assertEqual(load(save(self.root,obj)).store_id,'сессия-α')
    def test_paths_are_absolute_no_parent_env_or_nul(self):
        for path in ('client.key','$KEY_FILE','~/client.key','/tmp/../client.key','/tmp/\x00key',123):
            obj=copy.deepcopy(self.obj);obj['transport']['client_key']=path
            with self.subTest(path=path):self.reject(save(self.root,obj),'invalid_path')
        for path in ('relative.json','/tmp/\udcff',123):
            with self.subTest(config_path=repr(path)),self.assertRaises(DeploymentError):
                load_deployment(path,expected_sha256='0'*64)
    def test_config_bounded_even_with_matching_digest(self):
        self.reject(save(self.root,raw=b' '*(MAX_CONFIG_BYTES+1)),'file_limit_exceeded')
    def test_credential_caps_and_missing_files(self):
        pair=save(self.root,self.obj)
        (self.root/'ca.pem').write_bytes(b'x'*(MAX_CREDENTIAL_BYTES+1))
        self.reject(pair,'file_limit_exceeded')
        (self.root/'ca.pem').unlink();self.reject(pair,'file_access_failed')
    def test_symlink_and_fifo_refused_without_blocking(self):
        pair=save(self.root,self.obj);target=self.root/'original.json';pair[0].rename(target)
        pair[0].symlink_to(target);self.reject(pair,'file_access_failed')
        pair[0].unlink();os.mkfifo(pair[0],0o600);self.reject(pair,'not_regular_file')
    def test_credential_symlink_refused(self):
        pair=save(self.root,self.obj);key=self.root/'client.key';key.unlink();key.symlink_to(self.certs/'client.key')
        self.reject(pair,'file_access_failed')
    def test_permissions_and_owner(self):
        pair=save(self.root,self.obj);pair[0].chmod(0o666)
        self.reject(pair,'unsafe_file_permissions');pair[0].chmod(0o600)
        key=self.root/'client.key';key.chmod(0o644)
        self.reject(pair,'unsafe_file_permissions');key.chmod(0o600)
        (self.root/'ca.pem').chmod(0o664);self.reject(pair,'unsafe_file_permissions')
        (self.root/'ca.pem').chmod(0o644)
        if os.geteuid()!=0:
            with patch('os.geteuid',return_value=os.geteuid()+1):self.reject(pair,'untrusted_file_owner')
    def test_changed_credentials_rechecked_on_construction(self):
        d=load(save(self.root,self.obj));(self.root/'client.key').chmod(0o644)
        with self.assertRaises(DeploymentError):d.make_witness()
    def test_bad_pem_and_key_pair_fail_locally(self):
        pair=save(self.root,self.obj);(self.root/'ca.pem').write_bytes(b'bad pem')
        self.reject(pair,'invalid_tls_configuration')
        shutil.copyfile(self.certs/'ca.pem',self.root/'ca.pem')
        shutil.copyfile(self.certs/'other.key',self.root/'client.key')
        self.reject(pair,'invalid_tls_configuration')
    def test_encrypted_key_does_not_prompt_or_leak(self):
        encrypted=self.root/'encrypted.key'
        for password in ('fixture-only',''):
            with self.subTest(empty_password=not password):
                subprocess.run(['openssl','pkey','-in',str(self.root/'client.key'),'-aes-256-cbc',
                                '-passout','pass:'+password,'-out',str(encrypted)],check=True,capture_output=True,timeout=10)
                encrypted.chmod(0o600);self.obj['transport']['client_key']=str(encrypted)
                pair=save(self.root,self.obj)
                p=subprocess.run([sys.executable,'-m','tools.challenge_store.witness_config','check-config',
                                  '--config',str(pair[0]),'--config-sha256',pair[1]],
                                 input=b'',capture_output=True,timeout=10)
                self.assertEqual(p.returncode,1);self.assertEqual(p.stderr,b'')
                self.assertEqual(json.loads(p.stdout)['error'],'invalid_tls_configuration')
                self.assertNotIn(b'fixture-only',p.stdout);self.assertNotIn(str(encrypted).encode(),p.stdout)
    def test_cli_check_and_refusal_are_structured_no_network_or_secrets(self):
        pair=save(self.root,self.obj)
        for pin,code,status in [(pair[1],0,'configuration_valid'),('0'*64,1,'refused')]:
            out=io.StringIO()
            with redirect_stdout(out),patch('socket.create_connection',side_effect=AssertionError('network forbidden')):
                rc=main(['check-config','--config',str(pair[0]),'--config-sha256',pin])
            report=json.loads(out.getvalue());self.assertEqual(rc,code);self.assertEqual(report['status'],status)
            self.assertFalse(report['external_service_qualified']);self.assertEqual(report['authorization'],'blocked')
            self.assertNotIn(str(self.root),out.getvalue())


class ProbeTests(TLSFixture):
    def deployment(self, **changes):
        for name in ('ca.pem','client.pem','client.key'):
            shutil.copyfile(self.certs/name,self.root/name);(self.root/name).chmod(0o600)
        obj=document(self.root,port=self.cfg.port,pin=self.pins['server']);obj.update(changes)
        return load(save(self.root,obj))
    def test_ready_probe_reads_only_and_does_not_qualify_service(self):
        before=self.backend.read(ID);d=self.deployment();report=probe(d)
        self.assertEqual(report['status'],'ready_head_observed');self.assertEqual(report['head']['epoch'],0)
        self.assertFalse(report['external_service_qualified']);self.assertEqual(report['authorization'],'blocked')
        self.assertEqual(self.backend.read(ID),before)
        self.assertEqual([q['operation'] for q in self.server.requests],['read'])
        self.assertEqual(sorted(p.name for p in self.root.glob('*.db')),['witness.db'])
    def test_prepared_probe_never_finalizes_or_exposes_token(self):
        head=Prepared(0,'a'*64,'b'*64,'1'*32);self.backend.cas(ID,Ready(0,'a'*64),head)
        report=probe(self.deployment());self.assertEqual(report['status'],'prepared_head_observed')
        self.assertNotIn('token',report['head']);self.assertEqual(self.backend.read(ID),head)
        self.assertEqual([q['operation'] for q in self.server.requests],['read'])
    def test_absent_slot_not_automatically_enrolled(self):
        self.server.allowed.add('new-store');report=probe(self.deployment(store_id='new-store'))
        self.assertEqual(report['status'],'store_not_provisioned');self.assertIsNone(self.backend.read('new-store'))
        self.assertEqual([q['operation'] for q in self.server.requests],['read'])
    def test_wrong_pin_prevents_http(self):
        d=self.deployment();obj=document(self.root,port=self.cfg.port)
        d=load(save(self.root,obj))
        with self.assertRaises(WitnessTransportError):probe(d)
        self.assertEqual(self.server.requests,[])
    def test_unavailable_is_not_absence_and_no_retry(self):
        self.server.status=503
        with self.assertRaises(WitnessTransportError):probe(self.deployment())
        self.assertEqual(len(self.server.requests),1);self.assertEqual(self.backend.read(ID),Ready(0,'a'*64))
    def test_cli_probe_exit_statuses_and_read_only(self):
        d=self.deployment();path=self.root/'deployment.json'
        for mode,expected_status,code in [('ready','ready_head_observed',0),('prepared','prepared_head_observed',3),('failure','refused',1)]:
            if mode=='prepared':self.backend.cas(ID,Ready(0,'a'*64),Prepared(0,'a'*64,'b'*64,'1'*32))
            if mode=='failure':self.server.status=503
            p=subprocess.run([sys.executable,'-m','tools.challenge_store.witness_config','probe',
                              '--config',str(path),'--config-sha256',d.configuration_sha256],capture_output=True,timeout=10)
            self.assertEqual(p.returncode,code);self.assertEqual(p.stderr,b'')
            self.assertEqual(json.loads(p.stdout)['status'],expected_status);self.assertNotIn(str(self.root).encode(),p.stdout)
        self.assertEqual([q['operation'] for q in self.server.requests],['read']*3)


@unittest.skipUnless(os.environ.get('PROVENANCE_STORE_LIVE_TESTS')=='1','live Lean/native bridge')
class ConfiguredStoreTests(TLSFixture):
    def test_configured_four_file_acceptance_and_read_only_probe(self):
        from tools.challenge_store.store import Store, Controller
        from tools.challenge_store.files import submit_files
        from tests.test_provenance_files import package, expected, key_of
        cap=Controller();db=self.root/'registry.db';Store.initialize(db,cap)
        context=expected()['context'];key=key_of(context)
        with Store(db,controller=cap) as store:
            store.install_context('v1',context,cap);store.issue(key,cap)
            genesis=enrollment_checkpoint(store,'configured-store',cap)
        self.server.allowed.add('configured-store');self.backend.provision('configured-store',genesis)
        for name in ('ca.pem','client.pem','client.key'):
            shutil.copyfile(self.certs/name,self.root/name);(self.root/name).chmod(0o600)
        obj=document(self.root,port=self.cfg.port,pin=self.pins['server']);obj['store_id']='configured-store'
        deployment=load(save(self.root,obj))
        with AnchoredStore(db,store_id=deployment.store_id,witness=deployment.make_witness(),controller=cap) as store:
            before=store.inspect();count=len(self.server.requests)
            self.assertEqual(probe(deployment)['status'],'ready_head_observed')
            self.assertEqual([q['operation'] for q in self.server.requests[count:]],['read'])
            self.assertEqual(store.inspect(),before)
            result=submit_files(store,'configured-first','v1',package())
            self.assertEqual(result['redemption']['result']['newly_consumed']['record'],expected()['record'])
            submit_files(store,'configured-repeat','v1',package())
            self.assertEqual(len(store.inspect()['accepted']),1)
        with AnchoredStore(db,store_id=deployment.store_id,witness=deployment.make_witness()) as store:
            self.assertIn('confirmed_committed',store.resolve(key,'configured-first')['resolution']['result'])


if __name__=='__main__':unittest.main()

"""Real loopback TLS + test-only durable witness. Not external trust qualification."""
import copy
from dataclasses import replace
import hashlib
import http.server
import json
import os
from pathlib import Path
import socket
import sqlite3
import ssl
import subprocess
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
import http.client
from concurrent.futures import ThreadPoolExecutor
from tools.challenge_store.witness_https import (HTTPSWitness,WitnessTLSConfig,WitnessTransportError,
    head_to_wire,head_from_wire,encode_wire,decode_wire,parse_request,encode_response,MAX_BODY,PATH)
from tools.challenge_store.anchor import Ready,Prepared,AnchoredStore,enrollment_checkpoint,valid_transition
from tools.challenge_store.store import Store,Controller,StoreError
from tools.challenge_store.files import submit_files
from tests.test_provenance_files import package,expected,key_of

ID='store-one';SID='test-witness-service'

def certificates(root):
    def run(*args):subprocess.run(['openssl',*args],cwd=root,check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=20)
    run('req','-x509','-newkey','rsa:2048','-nodes','-days','2','-subj','/CN=Ephemeral Test CA',
        '-keyout','ca.key','-out','ca.pem','-addext','basicConstraints=critical,CA:TRUE','-addext','keyUsage=critical,keyCertSign,cRLSign')
    for name,purpose in [('server','serverAuth'),('client','clientAuth'),('other','clientAuth')]:
        run('req','-new','-newkey','rsa:2048','-nodes','-subj','/CN='+name,'-keyout',name+'.key','-out',name+'.csr')
        (root/(name+'.ext')).write_text('basicConstraints=critical,CA:FALSE\nkeyUsage=critical,digitalSignature,keyEncipherment\nextendedKeyUsage='+purpose+'\nsubjectKeyIdentifier=hash\nauthorityKeyIdentifier=keyid,issuer\n'+('subjectAltName=DNS:localhost\n' if name=='server' else ''))
        run('x509','-req','-in',name+'.csr','-CA','ca.pem','-CAkey','ca.key','-CAcreateserial','-days','2','-extfile',name+'.ext','-out',name+'.pem')
    run('x509','-req','-in','server.csr','-CA','ca.pem','-CAkey','ca.key','-CAcreateserial','-days','-1','-extfile','server.ext','-out','expired.pem')
    return {name:hashlib.sha256(ssl.PEM_cert_to_DER_cert((root/(name+'.pem')).read_text())).hexdigest() for name in ('server','client','other')}

class DurableTestWitness:
    """Only SQLite durability in local tests; this DB can itself be rolled back."""
    def __init__(self,path):
        self.path=path
        with self.connect() as db:db.execute('CREATE TABLE IF NOT EXISTS heads (id TEXT PRIMARY KEY, body BLOB NOT NULL)')
    def connect(self):
        db=sqlite3.connect(self.path,timeout=5);db.execute('PRAGMA journal_mode=WAL');db.execute('PRAGMA synchronous=FULL');return db
    def provision(self,identity,head):
        with self.connect() as db:db.execute('INSERT INTO heads VALUES (?,?)',(identity,encode_wire(head_to_wire(head))))
    def read(self,identity):
        with self.connect() as db:
            row=db.execute('SELECT body FROM heads WHERE id=?',(identity,)).fetchone()
            return None if row is None else head_from_wire(decode_wire(row[0]))
    def cas(self,identity,old,new):
        if not valid_transition(old,new):raise ValueError('invalid transition')
        with self.connect() as db:
            db.execute('BEGIN IMMEDIATE')
            row=db.execute('SELECT body FROM heads WHERE id=?',(identity,)).fetchone()
            if row is None or head_from_wire(decode_wire(row[0]))!=old:return False
            db.execute('UPDATE heads SET body=? WHERE id=?',(encode_wire(head_to_wire(new)),identity));return True

class TLSServer(http.server.ThreadingHTTPServer):
    daemon_threads=True
    def get_request(self):
        sock,address=super().get_request();sock.settimeout(2)
        try:return self.context.wrap_socket(sock,server_side=True),address
        except BaseException:sock.close();raise
    def handle_error(self,*args):pass

class Handler(http.server.BaseHTTPRequestHandler):
    protocol_version='HTTP/1.1'
    def log_message(self,*args):pass
    def do_POST(self):
        server=self.server
        pin=hashlib.sha256(self.connection.getpeercert(binary_form=True)).hexdigest()
        if pin!=server.client_pin:self.send_error(403);return
        if self.path!=PATH:self.send_error(404);return
        length=int(self.headers['Content-Length'])
        if length>MAX_BODY:self.send_error(413);return
        raw=self.rfile.read(length);q=parse_request(raw)
        server.requests.append(q)
        if q['server_id']!=SID or q['store_id'] not in server.allowed:self.send_error(403);return
        if server.mode=='stall':time.sleep(.4)
        if q['operation']=='read':result=server.backend.read(q['store_id'])
        else:result=server.backend.cas(q['store_id'],head_from_wire(q['expected']),head_from_wire(q['desired']))
        body=encode_response(raw,result)
        if server.mode=='lose_cas' and q['operation']=='cas':
            self.connection.shutdown(socket.SHUT_RDWR);self.connection.close();return
        if server.mode=='replay':body=server.previous
        else:server.previous=body
        if server.transform:body=server.transform(body)
        status=server.status
        self.send_response(status)
        self.send_header('Content-Type','application/json')
        self.send_header('Cache-Control','no-store')
        if server.mode!='missing_length':self.send_header('Content-Length',str(len(body)+ (3 if server.mode=='truncated' else 0)))
        if server.mode=='duplicate_length':self.send_header('Content-Length',str(len(body)))
        if server.mode=='chunked':self.send_header('Transfer-Encoding','chunked')
        if server.mode=='compressed':self.send_header('Content-Encoding','gzip')
        self.send_header('Connection','close');self.end_headers();self.wfile.write(body)
        self.close_connection=True

class WireTests(unittest.TestCase):
    def request(self):return dict(version=1,server_id=SID,store_id=ID,nonce='1'*64,operation='read')
    def test_ready_prepared_roundtrip(self):
        for head in (Ready(0,'a'*64),Prepared(3,'a'*64,'b'*64,'1'*32)):
            self.assertEqual(head_from_wire(decode_wire(encode_wire(head_to_wire(head)))),head)
    def test_malformed_heads(self):
        for obj in ({},None,dict(kind='ready',epoch=True,digest='a'*64),dict(kind='ready',epoch=1,digest='A'*64),dict(kind='prepared',epoch=1,digest='a'*64,next_digest='b'*64,token='short')):
            with self.subTest(obj=obj),self.assertRaises(WitnessTransportError):head_from_wire(obj)
    def test_strict_canonical_json(self):
        for raw in (b'{} ',b'{"x":1,"x":2}',b'{"x":1.0}',b'\xff',b'['*2000,b'0'*(MAX_BODY+1)):
            with self.subTest(raw=raw[:20]),self.assertRaises(WitnessTransportError):
                obj=decode_wire(raw)
                # Numeric wire values are further restricted by the typed schema.
                parse_request(encode_wire(obj))
    def test_request_fields_and_versions(self):
        q=self.request();self.assertEqual(parse_request(encode_wire(q)),q)
        for field,value in [('version',True),('nonce','old'),('server_id',''),('operation','reset')]:
            bad=dict(q);bad[field]=value
            with self.subTest(field=field),self.assertRaises(WitnessTransportError):parse_request(encode_wire(bad))
        bad=dict(q,extra=1)
        with self.assertRaises(WitnessTransportError):parse_request(encode_wire(bad))
    def test_cas_illegal_transition(self):
        q=dict(self.request(),operation='cas',expected=head_to_wire(Ready(1,'a'*64)),desired=head_to_wire(Ready(0,'a'*64)))
        with self.assertRaises(WitnessTransportError):parse_request(encode_wire(q))
    def test_response_exact_request_binding(self):
        raw=encode_wire(self.request());answer=decode_wire(encode_response(raw,None))
        self.assertEqual(answer['request_sha256'],hashlib.sha256(raw).hexdigest());self.assertIsNone(answer['result'])

class TLSFixture(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cert_temp=tempfile.TemporaryDirectory();cls.certs=Path(cls.cert_temp.name);cls.pins=certificates(cls.certs)
    @classmethod
    def tearDownClass(cls):cls.cert_temp.cleanup()
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.root=Path(self.temp.name)
        self.backend=DurableTestWitness(self.root/'witness.db');self.backend.provision(ID,Ready(0,'a'*64))
        self.start_server()
    def start_server(self):
        self.server=TLSServer(('127.0.0.1',0),Handler)
        ctx=ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER);ctx.minimum_version=ssl.TLSVersion.TLSv1_3
        ctx.load_cert_chain(self.certs/'server.pem',self.certs/'server.key');ctx.load_verify_locations(self.certs/'ca.pem');ctx.verify_mode=ssl.CERT_REQUIRED
        self.server.context=ctx;self.server.client_pin=self.pins['client'];self.server.backend=self.backend;self.server.allowed={ID}
        self.server.requests=[];self.server.mode='normal';self.server.transform=None;self.server.status=200;self.server.previous=b''
        self.thread=threading.Thread(target=self.server.serve_forever,daemon=True);self.thread.start()
        self.cfg=WitnessTLSConfig('localhost',self.server.server_address[1],SID,self.certs/'ca.pem',self.certs/'client.pem',self.certs/'client.key',self.pins['server'],1)
        self.client=HTTPSWitness(self.cfg)
    def tearDown(self):self.server.shutdown();self.server.server_close();self.thread.join();self.temp.cleanup()
    def assert_transport(self,fn):
        with self.assertRaises(WitnessTransportError):fn()

class HTTPSTests(TLSFixture):
    def test_real_read_cas_and_reopen(self):
        r=Ready(0,'a'*64);p=Prepared(0,'a'*64,'b'*64,'1'*32)
        self.assertEqual(self.client.read(ID),r);self.assertTrue(self.client.compare_and_set(ID,r,p))
        self.assertFalse(self.client.compare_and_set(ID,r,p));self.assertTrue(self.client.compare_and_set(ID,p,Ready(1,'b'*64)))
        self.server.shutdown();self.server.server_close();self.thread.join()
        self.backend=DurableTestWitness(self.root/'witness.db');self.start_server()
        self.assertEqual(self.client.read(ID),Ready(1,'b'*64))
    def test_distinct_nonces_and_old_response_rejected(self):
        self.client.read(ID);self.client.read(ID)
        self.assertNotEqual(self.server.requests[0]['nonce'],self.server.requests[1]['nonce'])
        self.server.mode='replay';self.assert_transport(lambda:self.client.read(ID))
    def test_binding_mutations(self):
        for field in ('server_id','store_id','nonce','operation','request_sha256','version'):
            def mutate(body):
                obj=decode_wire(body);obj[field]=True if field=='version' else 'other';return encode_wire(obj)
            self.server.transform=mutate
            with self.subTest(field=field):self.assert_transport(lambda:self.client.read(ID))
    def test_invalid_response_types_and_extra_fields(self):
        for change in [lambda o:dict(o,result={'kind':'ready','epoch':False,'digest':'a'*64}),lambda o:dict(o,extra=1)]:
            self.server.transform=lambda b:encode_wire(change(decode_wire(b)))
            self.assert_transport(lambda:self.client.read(ID))
        self.server.transform=lambda b:encode_wire(dict(decode_wire(b),result=1))
        self.assert_transport(lambda:self.client.compare_and_set(ID,Ready(0,'a'*64),Prepared(0,'a'*64,'b'*64,'1'*32)))
    def test_body_limits_and_bad_json(self):
        for body in (b'X'*(MAX_BODY+1),b'{',b'{}\n',b'{"x":1,"x":2}'):
            self.server.transform=lambda _,b=body:b
            self.assert_transport(lambda:self.client.read(ID))
    def test_http_framing_refusals(self):
        for mode in ('missing_length','duplicate_length','truncated','chunked','compressed'):
            self.server.mode=mode
            with self.subTest(mode=mode):self.assert_transport(lambda:self.client.read(ID))
    def test_http_errors_never_return_absence_or_false(self):
        for status in (301,302,401,403,404,409,429,500,503):
            self.server.status=status;self.assert_transport(lambda:self.client.read(ID))
    def test_pinned_leaf_before_http_request(self):
        client=HTTPSWitness(replace(self.cfg,server_cert_sha256='0'*64))
        self.assert_transport(lambda:client.read(ID));self.assertEqual(self.server.requests,[])
    def test_expired_server_certificate(self):
        self.server.context.load_cert_chain(self.certs/'expired.pem',self.certs/'server.key')
        pin=hashlib.sha256(ssl.PEM_cert_to_DER_cert((self.certs/'expired.pem').read_text())).hexdigest()
        client=HTTPSWitness(replace(self.cfg,server_cert_sha256=pin))
        self.assert_transport(lambda:client.read(ID));self.assertEqual(self.server.requests,[])
    def test_missing_client_certificate(self):
        context=ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT);context.load_verify_locations(self.certs/'ca.pem')
        connection=http.client.HTTPSConnection('localhost',self.cfg.port,context=context,timeout=1)
        try:
            with self.assertRaises((OSError,http.client.HTTPException)):
                connection.request('POST',PATH,body=b'{}');connection.getresponse()
        finally:connection.close()
        self.assertEqual(self.server.requests,[])
    def test_fresh_nonce_cannot_prove_honest_server_state(self):
        r=Ready(0,'a'*64);p=Prepared(0,'a'*64,'b'*64,'1'*32)
        self.client.compare_and_set(ID,r,p);self.client.compare_and_set(ID,p,Ready(1,'b'*64))
        self.server.transform=lambda b:encode_wire(dict(decode_wire(b),result=head_to_wire(r)))
        self.assertEqual(self.client.read(ID),r)  # explicit contract-violation counterexample
        self.assertEqual(self.backend.read(ID),Ready(1,'b'*64))
    def test_hostname_mismatch(self):
        client=HTTPSWitness(replace(self.cfg,host='127.0.0.1'))
        self.assert_transport(lambda:client.read(ID));self.assertEqual(self.server.requests,[])
    def test_untrusted_server_certificate(self):
        # A leaf unrelated to server chain is not a root authorizing the server.
        client=HTTPSWitness(replace(self.cfg,ca_file=self.certs/'other.pem'))
        self.assert_transport(lambda:client.read(ID));self.assertEqual(self.server.requests,[])
    def test_wrong_client_identity_and_store_scope(self):
        client=HTTPSWitness(replace(self.cfg,client_cert=self.certs/'other.pem',client_key=self.certs/'other.key'))
        self.assert_transport(lambda:client.read(ID));self.assertEqual(self.server.requests,[])
        self.assert_transport(lambda:self.client.read('other-store'))
    def test_socket_timeout_and_connection_failure(self):
        self.server.mode='stall';client=HTTPSWitness(replace(self.cfg,timeout_seconds=.05))
        self.assert_transport(lambda:client.read(ID))
        self.server.shutdown();self.server.server_close();self.thread.join()
        self.assert_transport(lambda:self.client.read(ID))
    def test_lost_cas_response_not_retried(self):
        self.server.mode='lose_cas';p=Prepared(0,'a'*64,'b'*64,'1'*32)
        self.assert_transport(lambda:self.client.compare_and_set(ID,Ready(0,'a'*64),p))
        self.assertEqual(len(self.server.requests),1);self.assertEqual(self.backend.read(ID),p)
    def test_missing_slot_is_only_explicit_null(self):
        self.server.allowed.add('absent');self.assertIsNone(self.client.read('absent'))
        self.assertIsNone(self.backend.read('absent'))
    def test_parallel_cas_only_one_winner(self):
        r=Ready(0,'a'*64)
        def attempt(i):return self.client.compare_and_set(ID,r,Prepared(0,'a'*64,format(i+1,'064x'),format(i+1,'032x')))
        with ThreadPoolExecutor(max_workers=4) as pool:out=list(pool.map(attempt,range(4)))
        self.assertEqual(out.count(True),1);self.assertEqual(out.count(False),3)
    def test_invalid_configuration_and_environment_keylog(self):
        for updates in [dict(host='https://host'),dict(port=True),dict(timeout_seconds=float('nan')),dict(timeout_seconds=0),dict(server_cert_sha256='x'*64)]:
            with self.subTest(updates=updates),self.assertRaises(WitnessTransportError):HTTPSWitness(replace(self.cfg,**updates))
        keylog=self.root/'must-not-exist.keys'
        with patch.dict(os.environ,{'SSLKEYLOGFILE':str(keylog),'HTTPS_PROXY':'http://127.0.0.1:1'}):
            client=HTTPSWitness(self.cfg);self.assertEqual(client.read(ID),Ready(0,'a'*64))
            self.assertIsNone(client._context.keylog_filename)
        self.assertFalse(keylog.exists())
        self.assertIsNone(self.client._context.keylog_filename)
        self.assertTrue(self.client._context.check_hostname);self.assertEqual(self.client._context.verify_mode,ssl.CERT_REQUIRED)

@unittest.skipUnless(os.environ.get('PROVENANCE_STORE_LIVE_TESTS')=='1','Enable Lean/SQLite full integration')
class HTTPSStoreTests(TLSFixture):
    def setUp(self):
        super().setUp();self.cap=Controller();self.dbpath=self.root/'registry.db';Store.initialize(self.dbpath,self.cap)
        cfg=expected()['context'];self.key=key_of(cfg)
        with Store(self.dbpath,controller=self.cap) as s:
            s.install_context('v1',cfg,self.cap);s.issue(self.key,self.cap);genesis=enrollment_checkpoint(s,'live-store',self.cap)
        self.server.allowed.add('live-store');self.backend.provision('live-store',genesis)
        self.store=AnchoredStore(self.dbpath,store_id='live-store',witness=self.client,controller=self.cap)
    def tearDown(self):self.store.close();super().tearDown()
    def test_four_file_path_over_mutual_tls(self):
        result=submit_files(self.store,'first','v1',package())
        self.assertEqual(result['redemption']['result']['newly_consumed']['record'],expected()['record'])
        submit_files(self.store,'again','v1',package())
        self.assertEqual(len(self.store.inspect()['accepted']),1)
        self.assertIn('confirmed_committed',self.store.resolve(self.key,'first')['resolution']['result'])
    def test_network_read_failure_preserves_db(self):
        before=self.store.inspect();self.server.status=503
        with self.assertRaises(StoreError) as e:submit_files(self.store,'bad','v1',package())
        self.assertEqual(e.exception.code,'anchor_unavailable');self.server.status=200
        self.assertEqual(self.store.inspect(),before)
    def test_lost_prepare_ack_blocks_and_is_not_auto_reset(self):
        self.server.mode='lose_cas'
        with self.assertRaises(StoreError) as e:submit_files(self.store,'lost','v1',package())
        self.assertEqual(e.exception.code,'anchor_indeterminate');self.server.mode='normal'
        with self.assertRaises(StoreError) as e:self.store.recover_anchor()
        self.assertEqual(e.exception.code,'anchor_recovery_blocked')
        self.assertIsInstance(self.client.read('live-store'),Prepared)

if __name__=='__main__':unittest.main()

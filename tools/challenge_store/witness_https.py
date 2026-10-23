"""Strict Witness v1 wire format and opt-in TLS 1.3 mutual-authentication client.

No automatic retries, redirects, proxy discovery, enrollment, or local fallback.
Server freshness, durable linearizable CAS and independent anti-rollback remain
external trust requirements; a nonce cannot prove honest server state selection.
"""
from dataclasses import dataclass
import hashlib
import hmac
import http.client
import math
from pathlib import Path
import re
import secrets
import ssl
from .anchor import Ready, Prepared, validate_head, valid_transition, _identity
from .bridge import dumps, loads

MAX_BODY=8192
PATH='/v1/witness'
VERSION=1

def _refuse_key_password():
    raise ValueError('encrypted_key_unsupported')

class WitnessTransportError(RuntimeError):
    """No write outcome may be inferred from this exception, including timeouts."""
    def __init__(self,code):self.code=code;super().__init__(code)

def _exact(obj,keys):
    if type(obj) is not dict or set(obj)!=set(keys):raise WitnessTransportError('invalid_wire')

def head_to_wire(head):
    validate_head(head)
    base=dict(kind='ready' if type(head) is Ready else 'prepared',epoch=head.epoch,digest=head.digest)
    if type(head) is Prepared:base.update(next_digest=head.next_digest,token=head.token)
    return base

def head_from_wire(obj):
    try:
        if type(obj) is not dict:raise ValueError()
        if obj.get('kind')=='ready':
            _exact(obj,('kind','epoch','digest'));head=Ready(obj['epoch'],obj['digest'])
        elif obj.get('kind')=='prepared':
            _exact(obj,('kind','epoch','digest','next_digest','token'))
            head=Prepared(obj['epoch'],obj['digest'],obj['next_digest'],obj['token'])
        else:raise ValueError()
        return validate_head(head)
    except (ValueError,TypeError,KeyError,RuntimeError) as e:
        raise WitnessTransportError('invalid_head') from e
    except Exception as e:
        # validate_head uses StoreError; malformed peer data is a transport refusal.
        raise WitnessTransportError('invalid_head') from e

def encode_wire(obj):
    raw=dumps(obj).encode('ascii')
    if len(raw)>MAX_BODY:raise WitnessTransportError('wire_limit_exceeded')
    return raw

def decode_wire(raw):
    if type(raw) is not bytes or len(raw)>MAX_BODY:raise WitnessTransportError('wire_limit_exceeded')
    try:
        obj=loads(raw.decode('ascii'))
        if encode_wire(obj)!=raw:raise ValueError('not canonical')
        return obj
    except (ValueError,UnicodeError,TypeError,RecursionError) as e:
        raise WitnessTransportError('invalid_wire') from e

def parse_request(raw):
    """Interoperability parser only: does not authenticate/authorize a request."""
    obj=decode_wire(raw)
    if type(obj) is not dict:raise WitnessTransportError('invalid_wire')
    common=('version','server_id','store_id','nonce','operation')
    op=obj.get('operation')
    _exact(obj,common if op=='read' else (*common,'expected','desired'))
    if type(obj['version']) is not int or obj['version']!=VERSION:raise WitnessTransportError('invalid_version')
    try:_identity(obj['server_id']);_identity(obj['store_id'])
    except Exception as e:raise WitnessTransportError('invalid_identity') from e
    if type(obj['nonce']) is not str or not re.fullmatch('[0-9a-f]{64}',obj['nonce']):raise WitnessTransportError('invalid_nonce')
    if op=='cas':
        a=head_from_wire(obj['expected']);b=head_from_wire(obj['desired'])
        if not valid_transition(a,b):raise WitnessTransportError('invalid_transition')
    elif op!='read':raise WitnessTransportError('invalid_operation')
    return obj

def encode_response(request_raw,result):
    """Response formatter; caller must perform authenticated durable service work."""
    q=parse_request(request_raw)
    if q['operation']=='read':value=None if result is None else head_to_wire(result)
    else:
        if type(result) is not bool:raise WitnessTransportError('invalid_result')
        value=result
    return encode_wire(dict(version=VERSION,server_id=q['server_id'],store_id=q['store_id'],
        nonce=q['nonce'],operation=q['operation'],request_sha256=hashlib.sha256(request_raw).hexdigest(),result=value))

@dataclass(frozen=True)
class WitnessTLSConfig:
    host: str
    port: int
    server_id: str
    ca_file: Path
    client_cert: Path
    client_key: Path
    server_cert_sha256: str
    timeout_seconds: float=5.0

class HTTPSWitness:
    def __init__(self,config: WitnessTLSConfig):
        self.config=config
        if type(config.host) is not str or len(config.host)>253 or not re.fullmatch('[A-Za-z0-9][A-Za-z0-9.-]*',config.host):raise WitnessTransportError('invalid_config')
        if type(config.port) is not int or not 1<=config.port<=65535:raise WitnessTransportError('invalid_config')
        if type(config.timeout_seconds) not in (int,float) or not math.isfinite(config.timeout_seconds) or not 0<config.timeout_seconds<=30:raise WitnessTransportError('invalid_config')
        if type(config.server_cert_sha256) is not str or not re.fullmatch('[0-9a-f]{64}',config.server_cert_sha256):raise WitnessTransportError('invalid_config')
        try:
            _identity(config.server_id)
            # Explicit context ignores environment SSLKEYLOGFILE and system CA roots.
            context=ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            context.minimum_version=ssl.TLSVersion.TLSv1_3
            context.maximum_version=ssl.TLSVersion.TLSv1_3
            context.hostname_checks_common_name=False
            context.load_verify_locations(cafile=str(config.ca_file))
            # Never prompt on a service's stdin for an encrypted key. Secret-store
            # integration is separate; this profile requires a protected plain PEM.
            context.load_cert_chain(str(config.client_cert),str(config.client_key),password=_refuse_key_password)
            context.set_alpn_protocols(['http/1.1'])
            self._context=context
        except Exception as e:raise WitnessTransportError('invalid_tls_configuration') from e

    def _exchange(self,store_id,operation,extra):
        try:_identity(store_id)
        except Exception as e:raise WitnessTransportError('invalid_identity') from e
        q=dict(version=VERSION,server_id=self.config.server_id,store_id=store_id,
               nonce=secrets.token_hex(32),operation=operation,**extra)
        raw=encode_wire(q);parse_request(raw)
        c=http.client.HTTPSConnection(self.config.host,self.config.port,timeout=self.config.timeout_seconds,context=self._context)
        try:
            c.connect()
            # Check the independently pinned leaf before sending any HTTP payload.
            pin=hashlib.sha256(c.sock.getpeercert(binary_form=True)).hexdigest()
            if not hmac.compare_digest(pin,self.config.server_cert_sha256):raise WitnessTransportError('server_pin_mismatch')
            c.request('POST',PATH,body=raw,headers={'Content-Type':'application/json','Accept':'application/json',
                      'Content-Length':str(len(raw)),'Connection':'close','Cache-Control':'no-store'})
            response=c.getresponse()
            if response.status!=200:raise WitnessTransportError('http_refused')
            headers={}
            for key,value in response.getheaders():headers.setdefault(key.lower(),[]).append(value)
            if 'transfer-encoding' in headers or 'content-encoding' in headers:raise WitnessTransportError('invalid_http_framing')
            lengths=headers.get('content-length',[])
            if len(lengths)!=1 or not re.fullmatch('0|[1-9][0-9]{0,4}',lengths[0]):raise WitnessTransportError('invalid_http_framing')
            length=int(lengths[0])
            if length>MAX_BODY:raise WitnessTransportError('wire_limit_exceeded')
            if headers.get('content-type')!=['application/json'] or headers.get('cache-control')!=['no-store']:
                raise WitnessTransportError('invalid_http_headers')
            body=response.read(length)
            if len(body)!=length:raise WitnessTransportError('truncated_response')
            answer=decode_wire(body)
            _exact(answer,('version','server_id','store_id','nonce','operation','request_sha256','result'))
            if type(answer['version']) is not int or any(answer[k]!=q[k] for k in ('version','server_id','store_id','nonce','operation')):
                raise WitnessTransportError('response_binding_mismatch')
            if answer['request_sha256']!=hashlib.sha256(raw).hexdigest():raise WitnessTransportError('response_binding_mismatch')
            if operation=='read':return None if answer['result'] is None else head_from_wire(answer['result'])
            if type(answer['result']) is not bool:raise WitnessTransportError('invalid_result')
            return answer['result']
        except WitnessTransportError:raise
        except (OSError,http.client.HTTPException,ValueError) as e:
            raise WitnessTransportError('transport_failure') from e
        finally:c.close()

    def read(self,store_id):return self._exchange(store_id,'read',{})
    def compare_and_set(self,store_id,expected,desired):
        if not valid_transition(expected,desired):raise WitnessTransportError('invalid_transition')
        return self._exchange(store_id,'cas',dict(expected=head_to_wire(expected),desired=head_to_wire(desired)))

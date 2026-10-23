"""Optional fixture generation; replay tests never execute this file.
Independent Python encoding and cryptography/OpenSSL signing, public RFC8032 seed.
Synthetic artifacts are arbitrary bytes; QCS/QCP mathematical validity is not claimed.
"""
import copy,hashlib,json
from pathlib import Path
from cryptography import __version__
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.backends.openssl.backend import backend

PREFIX=b'SIMLAB_PROVENANCE_V1_SHA256_ED25519:'

def nat(n):
    out=bytearray()
    while n>=128:out.append((n&127)|128);n>>=7
    out.append(n);return bytes(out)
def blob(b):return nat(len(b))+b
def text(s):return blob(s.encode('utf-8'))
def integer(i):return bytes([int(i<0)])+nat(abs(i))
def encode(m):
    b=b'QPM\x01'+b''.join(text(m[k]) for k in ('signerId','keyId','roleId','sessionId'))
    b+=blob(bytes(m['challenge']))+text(m['policyVersion'])
    for k in ('snapshot','profile'):b+=nat(m[k]['sizeBytes'])+blob(bytes(m[k]['digest']))
    b+=nat(m['n'])+nat(m['j'])+integer(m['epsilon'][0])+nat(m['epsilon'][1])+text(m['expectedContextId'])
    t=m['claimedTime']
    b+=b'\0' if t is None else b'\1'+text(t['scaleId'])+text(t['unitId'])+integer(t['value'])
    return b

def main():
    import sys
    root=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent/'vectors';root.mkdir()
    seed=bytes.fromhex('9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60')
    key=Ed25519PrivateKey.from_private_bytes(seed)
    snap=b'\x00snapshot\xff\n';prof=b'\x01profile\x00\xfe'
    bind=lambda b:dict(sizeBytes=len(b),digest=list(hashlib.sha256(b).digest()))
    m=dict(signerId='fixture-signer',keyId='rfc8032-key1',roleId='quota-auditor',sessionId='file-session',
      challenge=[16,32,48],policyVersion='file-policy-v1',snapshot=bind(snap),profile=bind(prof),
      n=3,j=1,epsilon=[-1,2],expectedContextId='file-context',claimedTime=dict(scaleId='test-clock',unitId='ticks',value=-3))
    variants={'good':m,'unicode':dict(m,signerId='Підписант 🌱',sessionId='сесія',expectedContextId='контекст',n=16384,j=128,epsilon=[-129,257])}
    for name,man in variants.items():
        d=root/name;d.mkdir();raw=encode(man);message=PREFIX+raw;signature=key.sign(message)
        key.public_key().verify(signature,message)
        pub=list(key.public_key().public_bytes_raw())
        ctx=dict(contextId=man['expectedContextId'],expectedSignerId=man['signerId'],expectedRoleId=man['roleId'],
          expectedSessionId=man['sessionId'],expectedPolicyVersion=man['policyVersion'],expectedN=man['n'],expectedJ=man['j'],
          expectedEpsilon=man['epsilon'],keyRegistry=[dict(signerId=man['signerId'],keyId=man['keyId'],roleId=man['roleId'],policyVersion=man['policyVersion'],pubKeyBytes=pub)],
          revokedKeys=[],activeChallenge=man['challenge'],trustedTimeWindow=dict(scaleId='test-clock',unitId='ticks',minTime=-5,maxTime=0))
        cfg=dict(expected=ctx,limits=dict(manifest=dict(maxManifestSizeBytes=4096,maxStringBytes=256,maxChallengeBytes=64),
          maxSnapshotSizeBytes=4096,maxProfileSizeBytes=4096,maxKeyRegistrySize=16,maxRevokedKeys=16,maxContextFieldBytes=256),allowMissingTimestamp=False)
        report=dict(signature='valid',keyAuthorization='authorized',contextBinding='matched',replay='challenge_matched',freshness='within_trusted_window',snapshotBinding='matched',profileBinding='matched',authorization='blocked')
        expected=dict(manifest=man,context=cfg,message=list(message),record=dict(payloadDigest=list(hashlib.sha256(message).digest()),pinnedContextVersion='v1',historicalReport=report))
        files={'manifest.bytes':raw,'signature.bytes':signature,'snapshot.bytes':snap,'profile.bytes':prof}
        for p,b in files.items():(d/p).write_bytes(b)
        (d/'expected.json').write_text(json.dumps(expected,ensure_ascii=False,indent=2)+'\n')
    good=root/'good';raw=(good/'manifest.bytes').read_bytes();sig=(good/'signature.bytes').read_bytes()
    negative={'manifest-tail':raw+b'\0','manifest-truncated':raw[:-1], 'manifest-version':raw[:3]+b'\2'+raw[4:],
              'manifest-uleb-padding':raw[:4]+bytes([raw[4]|128,0])+raw[5:],
              'manifest-invalid-utf8':raw[:5]+b'\xff'+raw[6:],
              'manifest-noncanonical-rational':encode(dict(m,epsilon=[-2,4]))}
    for name,raw in negative.items():
        d=root/name;d.mkdir();(d/'manifest.bytes').write_bytes(raw)
    d=root/'signature-mutated';d.mkdir();(d/'signature.bytes').write_bytes(bytes([sig[0]^1])+sig[1:])
    for name,b in [('snapshot',snap),('profile',prof)]:
        d=root/(name+'-mutated');d.mkdir();(d/(name+'.bytes')).write_bytes(bytes([b[0]^1])+b[1:])
    cases=[]
    for name in negative:cases.append(dict(id=name,field='manifest',file=name+'/manifest.bytes',phase='preflight',error='decode_rejected',sql='unchanged'))
    for field in ('signature','snapshot','profile'):
        cases.append(dict(id=field+'-mutated',field=field,file=field+'-mutated/'+field+'.bytes',phase='registered',reason='verification_rejected',sql='aborted_only'))
    for field in ('expectedSessionId','contextId','expectedPolicyVersion'):
        cases.append(dict(id='context-'+field,contextField=field,phase='registered',reason='verification_rejected',sql='aborted_only'))
    cases.append(dict(id='not-issued',issued=False,phase='registered',reason='challenge_not_issued',sql='aborted_only'))
    (root/'cases.json').write_text(json.dumps(cases,indent=2)+'\n')
    # Exact independent row snapshots. BLOBs have an explicit hex transport marker.
    golden={}
    e=json.loads((root/'good/expected.json').read_text())
    canon=lambda x:json.dumps(x,ensure_ascii=True,separators=(',',':'),sort_keys=True)
    asblob=lambda b:{'blob_hex':bytes(b).hex()}
    def initial(cfg,issued):
        c=cfg['expected'];scope=[c['contextId'],c['expectedSessionId'],c['expectedPolicyVersion']]
        kt=scope+[asblob(c['activeChallenge'])]
        return dict(context_versions=[['v1']+scope+[canon(cfg)]],active_contexts=[scope+['v1']],
                    challenge_entries=[kt+['ISSUED',None,None,None]] if issued else [],transactions=[]),kt
    before,kt=initial(e['context'],True);after=copy.deepcopy(before)
    r=e['record'];after['challenge_entries']=[kt+['CONSUMED',asblob(r['payloadDigest']),'v1',canon(r['historicalReport'])]]
    after['transactions']=[['first']+kt+[asblob(e['message']),'COMMITTED','newAcceptance',None,1]]
    golden['first']=dict(before=before,after=after)
    second=copy.deepcopy(after);second['transactions'].append(['second']+kt+[asblob(e['message']),'COMMITTED','historicalReturn',None,None])
    golden['second']=dict(before=after,after=second)
    for case in cases:
        cfg=copy.deepcopy(e['context'])
        if 'contextField' in case:cfg['expected'][case['contextField']]+='-mismatch'
        before,kt=initial(cfg,case.get('issued',True));after=copy.deepcopy(before)
        if case['phase']=='registered':after['transactions']=[ [case['id']]+kt+[asblob(e['message']),'ABORTED',None,case['reason'],None] ]
        golden[case['id']]=dict(before=before,after=after)
    (root/'expected_sql.json').write_text(json.dumps(golden,indent=2)+'\n')
    manifest=[]
    for p in sorted(root.rglob('*')):
        if p.is_file():manifest.append(dict(path=str(p.relative_to(root)),size=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
    (root/'manifest.json').write_text(json.dumps(dict(kind='synthetic-file-e2e-v1',generator='cryptography '+__version__,openssl=backend.openssl_version_text(),files=manifest),indent=2)+'\n')

if __name__=='__main__':main()

"""Synthetic conformance inputs, never real provenance. Public deterministic test seed."""
import ctypes
import hashlib
import json
from .bridge import ROOT

def fixture(bridge,session='session',challenge=None):
    p=json.loads((ROOT/'tools/provenance_native/profile.json').read_text())
    lib=ctypes.CDLL(p['library_path']); lib.sodium_init()
    pk=ctypes.create_string_buffer(32); sk=ctypes.create_string_buffer(64)
    seed=bytes(range(32))
    if lib.crypto_sign_seed_keypair(pk,sk,seed)!=0: raise RuntimeError('fixture keygen')
    snap=b'synthetic snapshot'; prof=b'synthetic profile'
    challenge=[10,20] if challenge is None else challenge
    def binding(b):return dict(sizeBytes=len(b),digest=list(hashlib.sha256(b).digest()))
    m=dict(signerId='signer',keyId='key',roleId='role',sessionId=session,challenge=challenge,
           policyVersion='policy',snapshot=binding(snap),profile=binding(prof),n=3,j=1,
           epsilon=[-1,2],expectedContextId='context',claimedTime=None)
    key=dict(scope=dict(contextId='context',sessionId=session,policyVersion='policy'),challenge=challenge)
    q=dict(key=key,contextVersion='v1',signed=dict(manifest=m,signature=[0]*64),snapshot=list(snap),profile=list(prof))
    msg=bytes(bridge.call({'binding':q})['message'])
    sig=ctypes.create_string_buffer(64); sz=ctypes.c_ulonglong()
    if lib.crypto_sign_detached(sig,ctypes.byref(sz),msg,ctypes.c_ulonglong(len(msg)),sk)!=0:
        raise RuntimeError('fixture signing')
    q['signed']['signature']=list(sig.raw)
    cfg=dict(expected=dict(contextId='context',expectedSignerId='signer',expectedRoleId='role',
         expectedSessionId=session,expectedPolicyVersion='policy',expectedN=3,expectedJ=1,expectedEpsilon=[-1,2],
         keyRegistry=[dict(signerId='signer',keyId='key',roleId='role',policyVersion='policy',pubKeyBytes=list(pk.raw))],
         revokedKeys=[],activeChallenge=challenge,trustedTimeWindow=None),
         limits=dict(manifest=dict(maxManifestSizeBytes=4096,maxStringBytes=128,maxChallengeBytes=64),
         maxSnapshotSizeBytes=4096,maxProfileSizeBytes=4096,maxKeyRegistrySize=16,maxRevokedKeys=16,maxContextFieldBytes=128),
         allowMissingTimestamp=True)
    return cfg,q

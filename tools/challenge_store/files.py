"""Bounded QPM/01 + detached signature + two artifact files to the existing store.

All loading/decoding/bridge/limit checks finish before register. Trusted context
comes from an immutable administrator-installed DB version, never from the package.
"""
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from .bridge import MAX_WIRE, dumps
from .store import StoreError

LOCAL_FILE_CAP = MAX_WIRE // 64
CHUNK_SIZE = 16384

class FileInputError(StoreError):
    pass

@dataclass(frozen=True)
class FilePackage:
    manifest: Path
    signature: Path
    snapshot: Path
    profile: Path

def _bounded_stream(stream, limit):
    """Read at most limit+1 bytes. Empty read is required to confirm EOF.
    The extra byte detects oversize; fstat size alone is never used as EOF.
    """
    data=bytearray()
    while True:
        part=stream.read(min(CHUNK_SIZE,limit+1-len(data)))
        if not isinstance(part,bytes): raise FileInputError('read_failure')
        if not part:return bytes(data)
        data.extend(part)
        if len(data)>limit:raise FileInputError('limit_exceeded')

def read_bounded(path, limit, *, exact=None):
    if type(limit) is not int or limit<0:raise FileInputError('invalid_limits')
    cap=min(limit,LOCAL_FILE_CAP)
    try:
        # O_NONBLOCK prevents FIFO open from hanging before we reject non-regular input.
        fd=os.open(path,os.O_RDONLY|os.O_NONBLOCK|os.O_CLOEXEC)
        try:
            if not stat.S_ISREG(os.fstat(fd).st_mode):
                raise FileInputError('unsupported_file_type')
            with os.fdopen(fd,'rb',buffering=0,closefd=False) as f:
                raw=_bounded_stream(f,cap)
        finally:
            os.close(fd)
    except OSError as e:
        raise FileInputError('read_failure',str(e)) from e
    if exact is not None and len(raw)!=exact:raise FileInputError('malformed_signature')
    return raw

def prepare_files(bridge, config, context_version, package):
    """No database mutation. Returns a complete in-memory request after EOF checks."""
    config=bridge.call({'context':config})
    limits=config['limits']
    manifest=read_bounded(package.manifest,limits['manifest']['maxManifestSizeBytes'])
    inp=dict(limits=limits['manifest'],bytes=list(manifest))
    decoded=bridge.call({'decodeManifest':inp})
    if 'fileError' in decoded:raise FileInputError(decoded['fileError'])
    m=decoded['manifest']
    # This second request crosses Python serialization again: compare all fields
    # against the original QPM bytes in Lean, not merely a byte-array JSON roundtrip.
    if bridge.call({'checkManifestBridge':dict(inp,manifest=m)}) is not True:
        raise FileInputError('bridge_mismatch')
    signature=read_bounded(package.signature,64,exact=64)
    snapshot=read_bounded(package.snapshot,limits['maxSnapshotSizeBytes'])
    profile=read_bounded(package.profile,limits['maxProfileSizeBytes'])
    ctx=config['expected'];challenge=ctx['activeChallenge']
    if challenge is None:raise FileInputError('missing_expected_challenge')
    key=dict(scope=dict(contextId=ctx['contextId'],sessionId=ctx['expectedSessionId'],
                        policyVersion=ctx['expectedPolicyVersion']),challenge=challenge)
    q=dict(key=key,contextVersion=context_version,signed=dict(manifest=m,signature=list(signature)),
           snapshot=list(snapshot),profile=list(profile))
    # Reserve space for state and protocol overhead before registering a transaction.
    if len(dumps(q).encode())>MAX_WIRE//4:raise FileInputError('transport_limit_exceeded')
    if bridge.call({'fileRequestFits':dict(config=config,request=q)}) is not True:
        raise FileInputError('limit_exceeded')
    binding=bridge.call({'binding':q})
    if binding['message']!=decoded['message'] or binding['key']!=key:
        raise FileInputError('bridge_mismatch')
    return q

def submit_files(store,tx_id,context_version,package):
    """Load first, then register and commit. No file is reopened after registration.
    register and commit remain separate transactions: a crash can leave PENDING,
    resolved or cancelled through the existing registry API.
    """
    cfg=dict(store.inspect()['contexts']).get(context_version)
    if cfg is None:raise FileInputError('unknown_context_version')
    q=prepare_files(store.bridge,cfg,context_version,package)
    store.register(tx_id,q)
    return store.commit_checked(tx_id,q)

"""Opt-in external witness gate. No production witness or local trust fallback.

Witness implementations must supply authenticated, fresh, linearizable, durable
read/CAS over an independently pinned store ID. Test doubles do not establish this.
All writers must use AnchoredStore; raw SQL/Store bypass and a compromised host are
outside this trusted-host profile. See ANCHOR.md before provisioning.
"""
import contextlib
from dataclasses import dataclass
import hashlib
import secrets
from typing import Protocol
from .bridge import dumps
from .store import Store, StoreError, HERE, normalize

MAX_EPOCH = 2**63-1
DOMAIN = 'SIMLAB_CHALLENGE_CHECKPOINT_V1'

@dataclass(frozen=True)
class Ready:
    epoch: int
    digest: str

@dataclass(frozen=True)
class Prepared:
    epoch: int
    digest: str
    next_digest: str
    token: str

Head = Ready | Prepared

class Witness(Protocol):
    """External trust contract, NOT a statement established by Python typing.

    read must return the latest authenticated head or authoritative absence.
    compare_and_set returns True only after durable atomic storage; False means
    a confirmed mismatch/no write. Lost responses/errors are indeterminate.
    Provisioning is separate, exclusive, controller-only, never automatic here.
    """
    def read(self, store_id: str) -> Head | None: ...
    def compare_and_set(self, store_id: str, expected: Head, desired: Head) -> bool: ...

class AnchorError(StoreError):
    pass

def _hex(s, n):
    return type(s) is str and len(s)==n and all(c in '0123456789abcdef' for c in s)

def validate_head(head):
    if type(head) not in (Ready,Prepared): raise AnchorError('anchor_invalid_response')
    if type(head.epoch) is not int or not 0<=head.epoch<=MAX_EPOCH or not _hex(head.digest,64):
        raise AnchorError('anchor_invalid_response')
    if type(head) is Prepared and (not _hex(head.next_digest,64) or not _hex(head.token,32) or head.epoch==MAX_EPOCH):
        raise AnchorError('anchor_invalid_response')
    return head

def valid_transition(old, new):
    """Required server-side rule as well as client-side validation; no resets/expiry."""
    validate_head(old);validate_head(new)
    if type(old) is Ready and type(new) is Prepared:
        return old.epoch==new.epoch and old.digest==new.digest
    if type(old) is Prepared and type(new) is Ready:
        return new.epoch==old.epoch+1 and new.digest==old.next_digest
    return False

def _identity(store_id):
    if type(store_id) is not str or not store_id or len(store_id.encode('utf-8'))>256:
        raise AnchorError('invalid_anchor_identity')
    return store_id

def checkpoint_digest(store_id, image):
    """Versioned semantic image, not raw SQLite/WAL bytes. Input must be validated.

    normalize sorts map entries; the acceptance log remains ordered. All context,
    report and transaction fields in the validated model image are covered.
    """
    body=dict(domain=DOMAIN,storeId=_identity(store_id),
        schema=hashlib.sha256((HERE/'schema.sql').read_bytes()).hexdigest(),
        profile=hashlib.sha256((HERE/'checkpoint_profile_v1.json').read_bytes()).hexdigest(),
        image=normalize(image))
    return hashlib.sha256(dumps(body).encode('utf-8')).hexdigest()

def enrollment_checkpoint(store, store_id, controller):
    """Review-only bootstrap value; never creates/replaces a witness slot.

    Run under an exclusive maintenance window before serving this DB. Independent
    provisioning must reject an already used ID, including after local rollback.
    """
    store._admin(controller)
    return Ready(0,checkpoint_digest(store_id,store.inspect()))

class AnchoredStore(Store):
    def __init__(self,path,*,store_id,witness,controller=None,timeout=2.0):
        self.store_id=_identity(store_id)
        self.witness=witness
        super().__init__(path,controller=controller,timeout=timeout)

    def _head(self):
        try: head=self.witness.read(self.store_id)
        except Exception as e: raise AnchorError('anchor_unavailable') from e
        if head is None: raise AnchorError('anchor_not_provisioned')
        return validate_head(head)

    def _cas(self,old,new):
        if not valid_transition(old,new): raise AnchorError('invalid_anchor_transition')
        try: result=self.witness.compare_and_set(self.store_id,old,new)
        except Exception as e: raise AnchorError('anchor_indeterminate') from e
        if type(result) is not bool: raise AnchorError('anchor_invalid_response')
        return result

    def _current(self,image):
        head=self._head()
        if type(head) is not Ready: raise AnchorError('anchor_recovery_required')
        if checkpoint_digest(self.store_id,image)!=head.digest:
            raise AnchorError('anchor_state_mismatch')
        return head

    def _phase(self,phase):
        """Internal diagnostic test seam; no policy or storage decision."""

    def _finish(self,prepared):
        ready=Ready(prepared.epoch+1,prepared.next_digest)
        if not self._cas(prepared,ready):
            # A concurrent recovery can have finalized precisely this checkpoint.
            if self._head()!=ready: raise AnchorError('anchor_indeterminate')
        return ready

    @contextlib.contextmanager
    def _transaction(self,write):
        prepared=None
        # BEGIN IMMEDIATE is held through all local work and external preparation.
        # Existing Store owns rollback/commit and SQLite error classification.
        with super()._transaction(write):
            old=self._read_image()
            head=self._current(old)
            yield
            if write:
                new_digest=checkpoint_digest(self.store_id,self._read_image())
                if new_digest!=head.digest:
                    if head.epoch==MAX_EPOCH: raise AnchorError('anchor_epoch_exhausted')
                    prepared=Prepared(head.epoch,head.digest,new_digest,secrets.token_hex(16))
                    self._phase('before_prepare')
                    if not self._cas(head,prepared): raise AnchorError('anchor_conflict')
                    self._phase('prepared')
        if prepared is not None:
            self._phase('local_committed')
            self._finish(prepared)
            self._phase('finalized')

    def recover_anchor(self):
        """Finalize only an externally prepared exact post-state. Never rewinds.

        Holds the SQL writer lock, but changes no registry rows. Not an application
        tx resolve and not permission to reissue/consume a challenge.
        """
        with Store._transaction(self,True):
            image=self._read_image();head=self._head()
            digest=checkpoint_digest(self.store_id,image)
            if type(head) is Ready:
                if digest!=head.digest: raise AnchorError('anchor_state_mismatch')
                return 'already_current'
            if digest!=head.next_digest: raise AnchorError('anchor_recovery_blocked')
            self._finish(head)
            return 'anchor_finalized'

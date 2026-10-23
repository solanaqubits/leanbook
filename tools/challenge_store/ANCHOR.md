# External witness gate v1

`anchor.AnchoredStore` is an opt-in software adapter around the existing Store
transaction boundary. It works with `submit_files` and all existing Store methods.
It is **not a deployed external root of trust**. No endpoint, credentials, TPM or
independent persistent service is bundled. The existing CLI still uses plain Store;
there is deliberately no command-line switch that silently picks a local witness.

## External contract and provisioning

The trusted controller supplies a stable `store_id` and a `Witness` object. Neither
may come from the incoming manifest or the rollbackable SQLite database. The witness
must implement authenticated, fresh, linearizable `read` and durable atomic
`compare_and_set`. Reads of cached signed heads are insufficient: an attacker could
replay an old, correctly signed head. The external service must enforce the same
`valid_transition` rule, one non-resettable history per ID, independent persistence,
access control and exclusive initial provisioning. Python protocols do not prove
these requirements. A malicious/broken witness can falsely acknowledge a write.

Bootstrap is explicit controller work in an exclusive maintenance window:

```python
from tools.challenge_store.anchor import AnchoredStore, enrollment_checkpoint
from tools.challenge_store.files import submit_files

# raw_store is a new or independently reviewed Store, held by its controller.
initial = enrollment_checkpoint(raw_store, independently_pinned_id, controller)
# Review and provision this exact Ready(0, digest) at the EXTERNAL service.
# Provisioning must refuse any previously used ID. No automatic reset/re-enrollment.
# external_witness is the separately implemented, qualified provider.
with AnchoredStore(db_path, store_id=independently_pinned_id,
                   witness=external_witness, controller=controller) as registry:
    result = submit_files(registry, tx_id, context_version, file_package)
```

Production enrollment must never approve the current rollbackable DB solely because
its local hash is self-consistent. The helper only calculates a review value; it
does not attest the snapshot or provision the provider. All writers/readers requiring
the guarantee must use the adapter. Raw SQL, the old Store/CLI, shared-process attacks,
live database replacement, provider rollback and compromised host code bypass its
boundary. It is not an OS access-control boundary. Qualify deployment separately.

## State commitment

A versioned, domain-separated SHA-256 commits to the externally pinned store ID,
exact schema/frozen v1 checkpoint-profile hashes and normalized validated logical image: immutable
contexts and active pointers, all challenge states/reports, exact transaction
bindings/outcomes, and ordered acceptance log. Maps are sorted; the log is ordered.
JSON is deterministic in this pinned Python/Lean profile. Raw DB pages, WAL layout,
free space and incidental file metadata are not hashed. Equivalent logical states
have the same digest. Collision resistance is an explicit cryptographic assumption;
there is no new formal theorem about this checkpoint serializer.

The frozen `checkpoint_profile_v1.json` contains the exact previous profile bytes.
Execution qualification now uses the separate corrected `profile.json`; see
[RUNTIME.en.md](RUNTIME.en.md). The checkpoint identifies format/state, not the
currently loaded binary. Trusted host runtime checks enforce the binary pin.

## Transaction protocol

1. Open the existing SQLite transaction (`BEGIN IMMEDIATE` for writes). Validate
   the current image and compare its digest with a fresh external `Ready` head.
2. Run the existing operation inside that uncommitted SQL transaction. A validation
   exception before preparation rolls back local changes and leaves the witness alone.
3. If the logical image changed, CAS `Ready(epoch, before)` to
   `Prepared(epoch, before, after, token)`. This confirms the exact intended post-state
   externally **before** local COMMIT. A false CAS rolls back locally. An ambiguous
   response cannot be interpreted as success or absence of an external change.
4. Commit SQLite. Then CAS that exact Prepared head to `Ready(epoch+1, after)`.
   Return the operation result only after confirmation. Unchanged operations and
   reads do not advance the witness. Epoch overflow refuses instead of wrapping.

This is a blocking protocol, not a distributed atomic commit proof. The SQLite
writer lock is held while preparing externally; provider timeouts must be bounded
by its implementation. Normal errors in decoding/preflight remain zero-diff.
A cryptographic rejection that records ABORTED is a changed logical state and is
anchored like any other mutation. Register and commitChecked are still separate
protected transactions. An application PENDING transaction is not an anchor Prepared.

## Crash recovery and limits

`recover_anchor()` acquires the same SQLite writer lock and changes **no registry
rows**. It finalizes a Prepared head only when the actual validated DB equals the
externally stored post-state. A matching Ready head returns `already_current`.
An absent head refuses; mismatching Ready indicates state mismatch; Prepared with
an old/different DB returns `anchor_recovery_blocked`. There is no timeout-based
abort, rollback-to-old-head command, local fallback or automatic new genesis.

Thus a crash after preparation but before local COMMIT may block the service even
if SQL rolled back correctly. Distinguishing this from malicious rollback requires
independent recovery evidence. Safety is preferred over automatic availability.
If local COMMIT succeeded but witness finalization/response failed, finishing the
matching checkpoint enables ordinary `resolve` without new acceptance. If a lost
response conceals a successful finalization, the fresh Ready head resolves it.
Fatal process crashes and corrupt hardware are not converted into Python errors.

`recover_anchor` confirms checkpoint alignment only, not the result of an arbitrary
application tx. Obtain that via guarded `resolve`. Physical authorization remains
blocked. Tests with an in-memory service in a separate process demonstrate finite
conformance and process-crash cases, not durable external anti-rollback deployment,
C/VFS correctness, power-loss safety or general linearizability.

SQLite transaction/isolation assumptions follow the existing pinned profile and
[transaction documentation](https://www.sqlite.org/lang_transaction.html) and
[isolation documentation](https://www.sqlite.org/isolation.html). These documents
are infrastructure references, not a proof of this adapter.

The suite also includes a deliberate counterexample: returning an old witness head
together with an old DB defeats detection. This is expected when the freshness/
independent-storage assumption is violated, and is not counted as deployed protection.

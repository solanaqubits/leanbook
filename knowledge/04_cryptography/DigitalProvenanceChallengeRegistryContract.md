---
id: DigitalProvenanceChallengeRegistryContract
language: en
section: cryptography
source: Verification/DigitalProvenanceChallengeRegistryContract.lean
source_sha256: 94fdbf3c00bd4a72322d8798a1ec6ed58507c5c81ace9300eda44bd5581b043d
novelty: not-assessed
status: reviewed
---

# Challenge registry atomic transition contract — epsilon262

[Lean source](../../Verification/DigitalProvenanceChallengeRegistryContract.lean). Pure model over epsilon258; old APIs preserved.
Trusted context versions are immutable and never reactivated. Issuance requires the
active externally supplied challenge. Transaction IDs bind exact signing messages
and keys. New acceptance updates the entry and terminal outcome atomically in the
model. Rejected transactions do not consume a challenge. Terminal abort excludes
late commit; response loss does not imply rollback.

Historical retries check pinned representation limits, statement digest and both
artifact sizes/digests; they do not assert current signature/key/time validity.
Resolution retains new-versus-historical outcome kind and is read-only. Unknown or
pending transactions remain indeterminate. No timeout establishes an abort.

The suite proves issuance/preflight requirements, at-most-one new acceptance,
record immutability, retry soundness, rejection preservation, read-only resolution,
terminal-abort soundness and blocked authorization. Supporting lemmas connect the
actual epsilon258 result and exact event log to arbitrary transition histories.
Tests use synthetic crypto callbacks, not a cryptographic implementation.

No concrete DB/IO linearizability, machine durability, anti-rollback, cryptographic
strength, physical clock/hardware or resource-bound claim. No new full beta gate
or public release. Third Obligation OPEN; novelty not-assessed.

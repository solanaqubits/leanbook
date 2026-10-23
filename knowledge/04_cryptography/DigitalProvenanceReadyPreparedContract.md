---
id: DigitalProvenanceReadyPreparedContract
language: en
section: cryptography
source: Verification/DigitalProvenanceReadyPreparedContract.lean
source_sha256: 16031c0ee371a0f5a61c11aadfac2ae224549363a78791b145c0ffd4cc169197
novelty: not-assessed
status: reviewed
---

# Ready / Prepared recovery refinement — epsilon276

[Lean source](../../Verification/DigitalProvenanceReadyPreparedContract.lean).
Development base: `3f6486da315dd8df5c6a76f073f81c997b8523af`.
This is an exact sequential-model proof, not verification of Python, SQLite or HTTPS.

The state contains a completed log, trusted ready/prepared head with exact pre/post
lists, pending state, phase, online flag and ghost acknowledged history. Context
and protected base are registry parameters. Request validation reuses epsilon255.
Acknowledgement follows completed persistence and a ready head. Ambiguous completion
has two histories: crash without sqlCommit, or sqlCommit followed by crash.
Persisted data are not automatically rolled back.

`related_step` maps each transition to zero or one epsilon259 action preserving
emitted output. Witness preparation and prepared-head recovery finalization may
stutter. The abstract anchor may lag the concrete head while protecting all acks.
`execution_simulation` preserves the ordered output list by induction on finite
histories. `forward_simulation` establishes the specified simulation obligations,
including the recovery-function relation.

`recovery_safety` derives acknowledged inclusion in restored.usedChallenges and
context preservation from reachability and the epsilon259 invariant.
`restored_base_preserved` preserves the protected base, including historical
duplicates. `recovered_replay_rejected` rejects exact bytes of acknowledged
challenges. `abstract_authorization_blocked` concerns only the formal output field.

`restoreCandidate?` requires offline state, a ready head and exact agreement with
the completed log, base and head contents. A prepared head returns none until
separate exact post-state finalization. Prepared-but-incomplete writes remain
offline in this bounded model. Epoch alone does not establish freshness. Trusted
current head, independent anchor and persistence of completed state are external
obligations. Comparing to completed specifies admissible images; it is not a way
to recover lost RAM after restart.

The original scoped work records30 executable scenarios covering crash boundaries,
context/base substitution, truncated/foreign tails, wrong bytes at equal length,
prepared/ready states, lost replies and replay, with registry examples. See the
original epsilon276 evidence for exact commands and versions. The separate SQLite
WAL-reset backport qualification is empirical, not an axiom or a syscall refinement
proof. Physical durability, concurrent linearizability, SHA-256 binding, witness
freshness, exactly-once delivery and hardware authorization remain unproved.
Authorization is blocked; organizational PAUSED/STANDBY/OPEN states are unchanged.

---
id: ActuatorArbitrationContract
language: en
section: distributed
source: Verification/ActuatorArbitrationContract.lean
source_sha256: a3ab744bbb4972c529b07dfde349371f8ab10665649390bc767ff4640f79227c
novelty: not-assessed
status: reviewed
---

# Arbitration: immutable receipts, dual version checks and fresh grants

[Section](README.md) · [Lean](../../Verification/ActuatorArbitrationContract.lean) ·
[Actuator contract](ExternalActuatorContract.en.md)

## Model and premises

One shared resource has multiple cases. Each case has its own version; the resource
version is shared. Natural-number identifiers, context and readiness masks are
abstract labels, not wire formats, cryptographic hashes or implemented permission masks.
A Request contains its identity, case, both expected versions, context and full decision.
Concrete encoding must bind the relevant policy, evidence, intent and fencing fields;
that correspondence is not proved. `policy : Request -> Bool` is an external validator.
Its authority, predecessor ownership, semantic safety and installation checks remain
explicit implementation obligations. The permissive policy in tests is only a fixture.

A fresh commit models an atomic serialization point for decision/grant registration.
It does not prove atomicity across BFT commitment, local installation and a grant service.
`applyRequest` first compares an existing receipt's complete Request: exact replay
returns the old result, conflicting replay rejects, and both leave state unchanged.
Only absent receipts proceed to both version checks, policy and FreshAction.
`accepted_iff` relates acceptance exactly to FreshCommit and the result grant.
Calling the raw mathematical `commit` without these conditions is not a valid transition.

## History, replay and exclusion

Every fresh decision, including KEEP_LOCKED, increments both its case version and the
shared resource version. Other case versions stay unchanged. A different fresh request
with the old resource version is rejected after the first commit, even for another case
(`anti_race_mutual_exclusion`). Already recorded requests take the earlier replay branch,
so the theorem does not say that every second call returns VersionConflict.

Arbitration leaves the entire imported actuator state, including permits, unchanged
(`history_preservation`, `run_history_preservation`). RESTORE_READINESS changes only the
abstract mask, versions and active grant; it cannot restore an old actuator permit.
This is not a claim about a safe mechanical position.
Receipts preserve complete request/result pairs through arbitrary finite Run sequences;
`no_second_commit` excludes another fresh acceptance of a recorded request and
`replay_after_interleaving` returns the original receipt without restoring authority.

AUTHORIZE_NEW_ACTION requires a new action distinct from its parent, an absent action
journal entry, a present parent entry, no prior allocation, an unused grant and a grant
distinct from predecessorGrant. Monotone usedGrants and allocatedActions prevent reuse
within this history; completeness of an externally restored history is not established.
`immutable_lineage_chain` records request/action/parent/predecessor/grant and
`run_lineage_preserved` retains old entries. The policy must still establish ownership
and semantic safety. A new identifier alone does not establish a different physical effect.
`inactive_old_grant_stays_inactive` excludes reactivation of a recorded inactive grant.
KEEP_LOCKED and RESTORE_READINESS create no grant; replay does not reactivate a cleared one.

## Composition and limits

`CombinedRun` interleaves arbitration with permitted steps of ExternalActuatorContract.
`combined_run_projection` projects arbitration to unchanged actuator states;
`combined_at_most_one_dispatch` reuses the original per-ID software dispatch bound,
and `combined_no_old_permit` preserves a spent permit. The relation between a real
grant and the actuator's authorization predicate is not supplied by this projection.

These are finite sequential transition and trace results, not an arbitration service,
PKI, codec, storage, driver or hardware implementation. Physical exactly-once effects,
progress, trusted fencing and concrete process refinement are not proved. Tests are
kernel/model regressions; no external acceptance scenario is represented as executed.
Novelty is not assessed. Verification is scoped, not a new full beta checkpoint.

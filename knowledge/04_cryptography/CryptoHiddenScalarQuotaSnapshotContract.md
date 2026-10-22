---
id: CryptoHiddenScalarQuotaSnapshotContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaSnapshotContract.lean
novelty: not-assessed
status: reviewed
---

# Typed quota cursor snapshots with verified restoration

Epsilon239, cryptography/bulletproofs-ipa; base cf04bb04fcd724cc2ca5709554e15b29418a50e7.
[Lean](../../Verification/CryptoHiddenScalarQuotaSnapshotContract.lean).

QuotaCursorSnapshot contains an unchecked natural bound and rational list. Restoration
checks length, reruns startQuotaSearch over the entire inclusive prefix, rejects found,
and accepts exhausted only when the saved row equals the reconstructed row exactly.
ValidSnapshot specifies the row and ∀t≤bound, ε<quotaDeficit n p t j; no probability
bounds on p or sign assumptions on ε are needed.

restore_sound/restore_complete/restore_isSome_iff/restore_none_iff characterize
acceptance. restore_eq_some_iff additionally matches the snapshot of the particular
output cursor. restore_snapshot proves exact round trip using cursor_ext and proof
irrelevance. restore_resume_eq proves full result equality to cold search for a
nonshrinking cap. restored_resume_correct also permits smaller caps without asserting
full cold-cursor equality at the smaller horizon.

The finite regressions contain 22 IO cases and 29 kernel examples including four
registry projections. Fraction-based expectations cover invalid rows and lengths,
n=0, negative tolerances, out-of-probability-range profiles p=-1 and p=2,
early success with a failing final row, and smaller/equal/larger continuations.
Changing a constant-row bound can remain valid. These are invariant checks, not
provenance checks. The module CLI audit permits only propext, Classical.choice and
Quot.sound; integrated scoped evidence additionally checks registry exports.

No byte codec, profile-function transfer, context authentication, authorization,
practical resource bound or rational bit-cost guarantee is supplied. Full prefix
recomputation is deliberate. This scoped addition is not a new full beta checkpoint.

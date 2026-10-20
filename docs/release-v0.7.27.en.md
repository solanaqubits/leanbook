# v0.7.27 — Weighted heavy tapes and arbitration contracts

This release exports `CryptoHiddenScalarHeavyTapeContract` (epsilon223) and
`ActuatorArbitrationContract` from pinned private source
`187963d00f7a79a707e2eeefe0dbec8b9ca1c502`.
The registry has 225 direct MasterSuite imports and 269 formal Lean sources.

## Weighted heavy tapes

The contract derives weighted qualifying-tape mass from global single-path acceptance.
Constant cutoffs, tape-dependent cutoffs and the expectation-one endpoint are handled
separately. A counterexample excludes substituting the average cutoff into the
constant-cutoff fractional bound. Good subsets may exclude an explicitly bounded mass.
A separate positive quota margin, together with the acceptance gap, supplies an actual
successful tape/seed pair of positive joint mass and witness-or-generator-relation
extraction. Original ProtocolPlan microseed laws and decoders remain unchanged.
Positive global acceptance alone does not prove positive extraction, efficient search,
ROM security or polynomial complexity.

## Serialized arbitration

The separate arbitration model uses per-case and shared-resource version checks,
immutable full-request receipts, fresh grant/action histories and retained lineage.
Exact replay returns the old result without reactivating authority. Arbitration steps
preserve the imported actuator state; projection of interleaved valid runs retains
its at-most-once software dispatch bound. Policy validation, concrete serialization,
grant installation/fencing and physical effects require separate implementation work.
This release does not deploy an arbitration service or certify hardware behavior.

## Verification scope

Independent public scoped checks cover cryptography and distributed directions,
affected integration, reviewed live tests and a single transitive axiom audit.
Only propext, Classical.choice and Quot.sound are allowed; no native-decide bypass.
Lake remains 0.7.1 and the full public beta basis remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1). No fresh full beta run is claimed.
Private SimLab documents, raw logs and Russian cards are excluded from this export.

[Heavy tapes](../knowledge/04_cryptography/CryptoHiddenScalarHeavyTapeContract.md) ·
[Arbitration](../knowledge/distributed/ActuatorArbitrationContract.en.md)

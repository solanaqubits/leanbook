# v0.7.25 — Threshold transfer to recursive fork quotas

This scoped release exports epsilon221, `CryptoHiddenScalarThresholdQuotaContract`,
from private source `9bb62485ea21a013262e448e92eb12505d92dde8`.
The public registry contains 221 direct MasterSuite imports and 265 formal Lean
sources, byte-identical to the private reference. Lake remains 0.7.1.

## Result

`quota_profile_mono` explicitly requires probability ranges before absorption;
`quota_density_mono` permits substitution of a lower density. Guarded local rates
retain exact snapshots and microseed multiplicities. A failed scalar check gives
zero accepted probability although a complete rejected transcript can exist;
a primitive query failure produces no child observation.

`acceptance_threshold_le` transfers single-path acceptance above a chosen threshold
to the existing recursive quota bound. `threshold_acquisition_lower` bounds the
actual collector's success probability. With a positive computed bound,
`threshold_positive_extracts` obtains a provenance-certified fork and a valid
witness OR a nontrivial generator relation through the existing extractor.
No new collector or extractor is introduced.

The fixed adversary tape, finite independent microseed product, common schedule
shape, budgets per depth and exact-snapshot decoders remain explicit. Sampling
is not restricted to heavy children. Sufficient budget/density margins establish
positivity; a zero conservative bound does not prove zero actual success.

## Validation scope

Independent public epsilon/scoped checks cover the module, affected integration
and batch dependencies, live unittest and one transitive axiom audit. Only
`propext`, `Classical.choice`, `Quot.sound` are allowed; no native-decide bypass.
The new regression package contains 51 Lean examples (including registry checks),
7 auxiliary regression theorems and 19 IO checks. It covers the actual collector,
positive 4/2/3 composition, rejected prefixes, depth zero, abort/wrong packets,
insufficient budgets, repeated microseed images, distinct reachable snapshots
with identical algebraic context, and zero conservative bounds with real success.

The full public beta basis remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1). This is not a new full beta run.
Random-tape averaging, external-process refinement, Fiat–Shamir/ROM,
polynomial complexity and hardware experiments are not established.
Private SimLab materials, Russian private cards and raw chats are not exported.

[Contract and hypotheses](../knowledge/04_cryptography/CryptoHiddenScalarThresholdQuotaContract.md)

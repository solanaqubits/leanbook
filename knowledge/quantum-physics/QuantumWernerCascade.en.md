---
id: QuantumWernerCascade
language: en
section: quantum-physics
source: Verification/QuantumWernerCascade.lean
source_sha256: 1d94acf30ef82ef5771a8cef6de3256c67e9b52e4587d6dece1cc20e08834928
novelty: not-assessed
status: reviewed
---

# QuantumWernerCascade

[Section](README.md) · [Lean source](../../Verification/QuantumWernerCascade.lean) ·
[Scope and verification](../../docs/quantum-v4.27.md)

A concrete specialization of the checked QuantumCascadedSwapping instrument.
Each preRound applies a specified CPTP channel before the complete Bell analyzer,
with spectator memory and a message-dependent output channel. preRound_map proves
agreement with the earlier system noisyOutcome on the system marginal.

wernerRound chooses central BC isotropic depolarization, perfect readout and
full-pair AD isotropic post depolarization. wernerCascade supplies a fixed fresh
Werner pair and fresh independent memory, using the same second-round parameters
for every delivered first message. Both environments can have arbitrary distinct
finite dimensions. The initial system input is a product of two Werner pairs,
independent of the first environment.

cascade_visibility_matrix proves a full matrix equality for the sum of all
successful two-round histories in the actual v4.26 cascade. The resulting visibility
is c2*b2*c1*b1*w*v*fresh. Both gate-noise factors of each round are included.
The successful aggregate has trace one, so its fidelity needs no extra
normalization. PSD, the target-overlap/scalar-transition bridge and nonincrease
relative to the first-round visibility are explicit consequences.

This proof uses chronological stages, Round.branch, cascadeBranch and Kraus
preparation. It does not assume the desired output matrix as a premise. Linearity
allows aggregation of the first messages because the continuation is identical
for each message in this specialization.

## Theorems

- [`QuantumWernerCascade.preStages_ideal`](../../Verification/QuantumWernerCascade.lean#L31)
- [`QuantumWernerCascade.preStages_run`](../../Verification/QuantumWernerCascade.lean#L36)
- [`QuantumWernerCascade.preRound_micro`](../../Verification/QuantumWernerCascade.lean#L48)
- [`QuantumWernerCascade.preRound_map`](../../Verification/QuantumWernerCascade.lean#L59)
- [`QuantumWernerCascade.wernerRound_accepted`](../../Verification/QuantumWernerCascade.lean#L101)
- [`QuantumWernerCascade.uniform_continuation`](../../Verification/QuantumWernerCascade.lean#L110)
- [`QuantumWernerCascade.cascade_visibility_matrix`](../../Verification/QuantumWernerCascade.lean#L117)
- [`QuantumWernerCascade.cascade_visibility_trace`](../../Verification/QuantumWernerCascade.lean#L147)
- [`QuantumWernerCascade.cascade_fidelity_transition`](../../Verification/QuantumWernerCascade.lean#L155)
- [`QuantumWernerCascade.cascade_fidelity_nonincrease`](../../Verification/QuantumWernerCascade.lean#L171)
- [`QuantumWernerCascade.cascade_visibility_positive`](../../Verification/QuantumWernerCascade.lean#L182)
- [`QuantumWernerCascade.verification_suite`](../../Verification/QuantumWernerCascade.lean#L208)

## Limits

The scalar law is tied to the stated Werner inputs, depolarizing channels and
perfect readout. It is not a universal fidelity law for CPTP maps, correlated
resources, adaptive feedback or postselection. No purification circuit, retained
memory process tensor, or arbitrary-number-of-rounds operator instrument is
formalized here. Finite iteration and limits concern the proved scalar recurrence.
Counts include auxiliary and registry theorems, not independent scientific results.

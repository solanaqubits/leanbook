---
id: QuantumNoisySwapping
language: en
section: quantum-physics
source: Verification/QuantumNoisySwapping.lean
source_sha256: 0f01f25be82e491177b1ebb346dc6254cfd606073efe62659dc05c8de1daa946
novelty: not-assessed
status: reviewed
---

# QuantumNoisySwapping

[Section](README.md) · [Lean source](../../Verification/QuantumNoisySwapping.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Noisy classical labels after ideal swapping. All formulas are derived from
Born weights and the actual correction selected by the reported label. Detection
is outcome-independent and misreporting is symmetric; conditioning requires a
strictly positive detection probability.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `joint_nonnegative`
- `reported_mass_formula`
- `accepted_mass_formula`
- `lost_mass_formula`
- `complete_event_mass`
- `correctedKet_eq`
- `corrected_density_positive`
- `corrected_density_trace`
- `miscorrection_overlap`
- `row_density_formula`
- `bell_projector_trace`
- `labelMixture_positive`
- `labelMixture_trace`
- `labelMixture_overlap`
- `accepted_density_formula`
- `accepted_density_trace`
- `normalized_accepted_eq`
- `conditional_matrix`
- `conditional_fidelity`
- `success_weighted_overlap`
- `conditional_after_depolarization`
- `no_detection_no_success`
- `detection_does_not_change_conditional`
- `correctOuter_double`
- `pure_pair_double`
- `raw_branch_density`
- `circuit_accepted_density_sound`
- `zero_detection_not_conditionable`
- `reported_marginals_ignore_corruption`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

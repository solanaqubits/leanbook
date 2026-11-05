---
id: QuantumSwappingInstrument
language: en
section: quantum-physics
source: Verification/QuantumSwappingInstrument.lean
source_sha256: fc161f2047a1ff7b46c39046cd72eed56ce3ee71d23a27502173e1f2d3b061a4
novelty: not-assessed
status: reviewed
---

# QuantumSwappingInstrument

[Section](README.md) · [Lean source](../../Verification/QuantumSwappingInstrument.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

A linear accepted swapping instrument from 16×16 to 4×4 matrices.
Complete positivity is proved through an independently defined ancillary block
extension. State normalization is separate from the linear instrument.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `weight_nonnegative`
- `weight_sum`
- `sqrt_sandwich`
- `accepted_kraus`
- `accepted_add`
- `accepted_smul`
- `accepted_sum`
- `accepted_real_smul`
- `ensemble_independent`
- `extension_kraus`
- `completely_positive`
- `accepted_positive`
- `kraus_effect`
- `effect_formula`
- `effect_positive`
- `effect_le_identity`
- `full_detection_effect`
- `accepted_trace`
- `lost_positive`
- `lost_trace`
- `trace_balance`
- `trace_nonincreasing`
- `trace_preserving_full_detection`
- `acceptance_bounds`
- `trace_eq_probability`
- `product_component_refinement`
- `bell_diagonal_refinement`
- `bell_diagonal_probability`
- `bell_diagonal_conditional`
- `born_nonnegative`
- `born_total`
- `acceptance_born_formula`
- `ghz_born_probabilities`
- `ghz_acceptance_not_uniform_average`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

---
id: QuantumSelectiveSwapping
language: en
section: quantum-physics
source: Verification/QuantumSelectiveSwapping.lean
source_sha256: 4d4d1ce120daf9ab6cc95ebcaba019c071dd9036b2429c33ebcb8729b75ee1bd
novelty: not-assessed
status: reviewed
---

# QuantumSelectiveSwapping

[Section](README.md) · [Lean source](../../Verification/QuantumSelectiveSwapping.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

General classical readout and selective event loss on the ideal two-pair
swapping circuit. The accepted density is derived from actual circuit amplitudes.
Conditioning is available only at positive success mass.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `joint_formula`
- `joint_nonnegative`
- `accepted_mass_formula`
- `accepted_mass_nonnegative`
- `complete_event_mass`
- `accepted_mass_le_one`
- `row_positive`
- `row_trace`
- `row_overlap`
- `accepted_positive`
- `accepted_density_rows`
- `accepted_trace`
- `circuit_density_sound`
- `correct_mass_bounds`
- `accepted_overlap`
- `conditional_fidelity`
- `conditional_fidelity_bounds`
- `constant_rows_conditional`
- `symmetric_confusion_rows`
- `symmetric_confusion_loss_invariant`
- `symmetric_joint`
- `symmetric_mass`
- `symmetric_density`
- `symmetric_conditional`
- `biased_mass`
- `biased_correct_mass`
- `biased_positive`
- `selection_bias_counterexample`
- `zero_mass_iff`
- `zero_mass_zero_density`
- `fidelity_eq_iff_balance`
- `constant_accuracy_fidelity`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

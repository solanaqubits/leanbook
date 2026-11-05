---
id: QuantumPauliMatrix
language: en
section: quantum-physics
source: Verification/QuantumPauliMatrix.lean
source_sha256: 792e67953446cf623d408c34d41dec7f4815f54876be1ec080b2cb3a9b963161
novelty: not-assessed
status: reviewed
---

# QuantumPauliMatrix

[Section](README.md) · [Lean source](../../Verification/QuantumPauliMatrix.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Four-phase Pauli multiplication and CNOT conjugation are connected to explicit matrices over Gaussian integers. The bounded integer channel interface retains exact numerators separately from flooring. This operator model alone does not establish Born probabilities.

Four-phase Pauli multiplication and CNOT conjugation are connected to explicit matrices over Gaussian integers. The bounded integer channel interface retains exact numerators separately from flooring. This operator model alone does not establish Born probabilities.

## Checked declarations

- `ga_assoc`
- `ga_comm`
- `gm_assoc`
- `gm_comm`
- `gm_add`
- `gm_zero`
- `gm_one`
- `sum_scale`
- `four_mul`
- `sum_tensor_term`
- `tensor_mul`
- `scale_mul`
- `tensor_scales`
- `scale_scale`
- `phase_one_value`
- `phase_mul_sound`
- `axis_mul_sound`
- `scalar_identity_mul`
- `mulPauli4Q_matrix_sound`
- `cnot_matrix_sound`
- `channel_numerator_bounds`
- `channel_rounding_bound`
- `cnot_self_adjoint`
- `cnot_involutive_matrix`
- `cnot_conjugation_sound`
- `noncommuting_product_keeps_imaginary_phase`
- `channel_zero_noise`
- `channel_full_noise`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

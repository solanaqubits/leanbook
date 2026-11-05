---
id: QuantumPauliDensityBridge
language: en
section: quantum-physics
source: Verification/QuantumPauliDensityBridge.lean
source_sha256: 42d47dd9660966911d85be6abb30fcbe7c9ef0ca872703b0a0e8a14ab2e13784
novelty: not-assessed
status: reviewed
---

# QuantumPauliDensityBridge

[Section](README.md) · [Lean source](../../Verification/QuantumPauliDensityBridge.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

# Exact Pauli embedding and typed two-qubit depolarization

The parameter is the mixing probability with I₄/4, not the probability of a
nonidentity single-qubit Pauli error. Born weights and conditional Bell states
are reused from the existing ideal swapping protocol. No detector model or
fault-tolerant circuit threshold is asserted.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `toComplex_add`
- `toComplex_mul`
- `toComplex_conjugate`
- `toComplex_injective`
- `sumBasis_embedding`
- `embed_multiplication`
- `embed_adjoint`
- `pauli_complex_matrix_sound`
- `cnot_complex_conjugation_sound`
- `probability_bounds`
- `maximallyMixed_positive`
- `maximallyMixed_trace`
- `depolarize_positive`
- `depolarize_trace`
- `targetOverlap_add`
- `targetOverlap_real_smul`
- `maximallyMixed_overlap`
- `depolarize_overlap`
- `channelNumerator_matrix_sound`
- `channelFloor_matrix_error`
- `correctedSwap_overlap`
- `born_and_noisy_conditional_fidelity`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

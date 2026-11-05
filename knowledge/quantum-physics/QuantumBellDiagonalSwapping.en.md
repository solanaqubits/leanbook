---
id: QuantumBellDiagonalSwapping
language: en
section: quantum-physics
source: Verification/QuantumBellDiagonalSwapping.lean
source_sha256: c7e3f6bee0aa13ecd16232a6366fd613659ddf6c88416a68b3bf69692a220c31
novelty: not-assessed
status: reviewed
---

# QuantumBellDiagonalSwapping

[Section](README.md) · [Lean source](../../Verification/QuantumBellDiagonalSwapping.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Independent Bell-diagonal inputs through the checked swapping circuit and
an arbitrary classical readout with selective loss. Normalized output is defined
only for positive success probability.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `component_positive`
- `component_trace`
- `accepted_positive`
- `accepted_trace`
- `circuit_density_sound`
- `event_mass_formula`
- `targetOverlap_sum`
- `projector_overlap`
- `accepted_overlap`
- `conditional_fidelity`
- `perfect_mass`
- `perfect_component`
- `ideal_density_from_circuit`
- `ideal_conditional_density`
- `ideal_fidelity`
- `ideal_inputs_recover_v49`
- `uniform_bell_sum`
- `uniform_input_erases_ideal_output`
- `visibility_product_valid`
- `isotropic_visibility_product`
- `isotropic_output_fidelity`
- `density_overlap`
- `scalar_fidelity_insufficient`
- `null_event_density`
- `ideal_inputs_conditional`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

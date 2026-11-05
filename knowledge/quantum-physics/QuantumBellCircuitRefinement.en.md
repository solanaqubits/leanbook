---
id: QuantumBellCircuitRefinement
language: en
section: quantum-physics
source: Verification/QuantumBellCircuitRefinement.lean
source_sha256: 0f418f873d3780c406c81a33ee3a0aab6c811ae3951c0614b151b2c254559e83
novelty: not-assessed
status: reviewed
---

# QuantumBellCircuitRefinement

[Section](README.md) · [Lean source](../../Verification/QuantumBellCircuitRefinement.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Ideal Bell measurement as CNOT, Hadamard on the control, and computational
readout. The measured central register is computational; undoing the analysis
unitary gives the Bell-projector instrument. No noisy detector is modeled.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `cnot_agrees_with_gaussian_matrix`
- `analysis_row`
- `analysis_unitary_left`
- `analysis_unitary_right`
- `branch_equals_bell_contraction`
- `instrument_equals_bell_projection`
- `readout_norm`
- `circuit_born_probability`
- `circuit_feedforward`
- `circuit_density_eq_corrected_state`
- `circuit_density_valid`
- `circuit_then_cptp_fidelity`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

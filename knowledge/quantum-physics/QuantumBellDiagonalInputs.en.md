---
id: QuantumBellDiagonalInputs
language: en
section: quantum-physics
source: Verification/QuantumBellDiagonalInputs.lean
source_sha256: 1ec0a0e3eeceee67f6fcdbca8674a14d41ad4af5d7dc435c1eb861789ee61b5a
novelty: not-assessed
status: reviewed
---

# QuantumBellDiagonalInputs

[Section](README.md) · [Lean source](../../Verification/QuantumBellDiagonalInputs.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Independent Bell-diagonal input pairs. Pure-component swapping is derived
from the gate circuit, retaining phases at ket level. Density identities remove
only global phases, not arbitrary relative phases.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `xor_cancel`
- `xor_zero_iff`
- `branch_amplitude`
- `pair_norm_smul`
- `component_born_probability`
- `correction_smul`
- `signed_half_density`
- `correction_density`
- `raw_corrected_density`
- `density_positive`
- `density_trace`
- `product_density_tensor`
- `input_density_tensor`
- `input_positive`
- `input_trace`
- `mixed_born_probability`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

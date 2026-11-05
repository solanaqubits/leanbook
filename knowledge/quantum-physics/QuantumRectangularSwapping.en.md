---
id: QuantumRectangularSwapping
language: en
section: quantum-physics
source: Verification/QuantumRectangularSwapping.lean
source_sha256: dbe7a68178e4395b2ff2fb3122cdb7260ded7f3494ca9b616e21517f318dd31d
novelty: not-assessed
status: reviewed
---

# QuantumRectangularSwapping

[Section](README.md) · [Lean source](../../Verification/QuantumRectangularSwapping.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Rectangular Bell contractions and Pauli feed-forward on arbitrary four-qubit
amplitudes. Input basis is ((A,B),(C,D)); output basis is (A,D).

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `reduction_amplitudes`
- `correction_amplitudes`
- `branch_amplitudes`
- `correction_unitary`
- `reduction_effect`
- `branch_effect`
- `central_projector_positive`
- `bell_completeness`
- `central_completeness`
- `sandwich_pure`
- `branch_pure_density`
- `component_refinement`
- `sandwich_trace`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

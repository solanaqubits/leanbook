---
id: QuantumTwoQubitCPTP
language: en
section: quantum-physics
source: Verification/QuantumTwoQubitCPTP.lean
source_sha256: d19eade99b8bc2264562c5434e9f210f8c22efc89914b9a9cc9a7b4f2bda1c30
novelty: not-assessed
status: reviewed
---

# QuantumTwoQubitCPTP

[Section](README.md) · [Lean source](../../Verification/QuantumTwoQubitCPTP.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

A trace-preserving linear extension of the two-qubit depolarizing state map.
The mixing probability is bounded. Complete positivity is quantified over every
finite ancillary dimension and proved using an independently defined block map.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `unit_sandwich`
- `unit_sum`
- `unit_adjoint`
- `unit_reverse_product`
- `diagonal_unit_sum`
- `sqrt_sandwich`
- `kraus_exact`
- `kraus_none_norm`
- `kraus_some_norm`
- `kraus_completeness`
- `linearChannel_trace`
- `linearChannel_add`
- `linearChannel_smul`
- `state_map_agrees`
- `extension_kraus`
- `completely_positive`
- `extension_trace_preserving`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

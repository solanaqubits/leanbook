---
id: QuantumGeneralBellReadout
language: en
section: quantum-physics
source: Verification/QuantumGeneralBellReadout.lean
source_sha256: 3abf6baaad56056cadb0bba65a7e86ee9596f706c1c80990cc0fb2a63425561d
novelty: not-assessed
status: reviewed
---

# QuantumGeneralBellReadout

[Section](README.md) · [Lean source](../../Verification/QuantumGeneralBellReadout.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

An arbitrary classical channel after ideal Bell measurement, with
outcome-dependent registration. The stochastic constraints are carried by the
input type; there is no symmetry or equal-efficiency assumption.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `confusion_le_one`
- `observation_nonnegative`
- `observation_row_sum`
- `symmetric_weights`
- `operation_kraus`
- `all_operations`
- `trace_total`
- `extension_kraus`
- `branch_completely_positive`
- `operation_positive`
- `outcomeProbability_nonnegative`
- `outcomeProbability_total`
- `outcomeProbability_le_one`
- `symmetric_operation`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

---
id: QuantumNoisyBellInstrument
language: en
section: quantum-physics
source: Verification/QuantumNoisyBellInstrument.lean
source_sha256: 2e76c664335d354eb228b6bdc0cae63fd0474496078e30698739a07ab0bc12a7
novelty: not-assessed
status: reviewed
---

# QuantumNoisyBellInstrument

[Section](README.md) · [Lean source](../../Verification/QuantumNoisyBellInstrument.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Classical postprocessing of ideal Bell measurement: outcome-independent
registration and symmetric misreporting among three wrong labels. Lost events
retain the nonselective measured state. These are modeling assumptions, not
properties inferred for a detector.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `sum_bell`
- `confusion_nonnegative`
- `confusion_row_sum`
- `confusion_column_sum`
- `observation_nonnegative`
- `observation_row_sum`
- `operation_kraus`
- `all_operations`
- `nonselective_trace`
- `trace_total`
- `extension_kraus`
- `branch_completely_positive`
- `operation_positive`
- `outcomeProbability_nonnegative`
- `outcomeProbability_total`
- `outcomeProbability_le_one`
- `projector_matches_circuit`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

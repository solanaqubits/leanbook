---
id: QuantumOutcomeInstrument
language: en
section: quantum-physics
source: Verification/QuantumOutcomeInstrument.lean
source_sha256: e90f19c8fc9e7a98b4cc9d47941e000311c2d796e362e6273dffa29e8b3cc670
novelty: not-assessed
status: reviewed
---

# QuantumOutcomeInstrument

[Section](README.md) · [Lean source](../../Verification/QuantumOutcomeInstrument.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

A finite instrument with four reported Bell labels and one rejection outcome.
Microscopic true labels remain hidden when classical readout is noisy.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `lift_family`
- `family_cp`
- `micro_kraus`
- `reported_family`
- `reject_family`
- `micro_cp`
- `reported_cp`
- `reject_cp`
- `micro_positive`
- `reported_positive`
- `reported_sum`
- `outcome_cp`
- `outcome_positive`
- `outcome_add`
- `outcome_smul`
- `outcome_total`
- `outcome_total_trace`
- `outcome_trace_nonincreasing`
- `full_detection_no_reject`
- `outcome_probability_nonnegative`
- `outcome_probability_total`
- `outcome_probability_le_one`
- `reported_probability_sum`
- `reject_probability`
- `micro_probability_born`
- `reported_probability_born`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

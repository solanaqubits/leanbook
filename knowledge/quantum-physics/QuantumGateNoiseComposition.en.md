---
id: QuantumGateNoiseComposition
language: en
section: quantum-physics
source: Verification/QuantumGateNoiseComposition.lean
source_sha256: 2cb1098e20a4076035bf859fc786a7e4218244041716003fce3ba27ec55677b8
novelty: not-assessed
status: reviewed
---

# QuantumGateNoiseComposition

[Section](README.md) · [Lean source](../../Verification/QuantumGateNoiseComposition.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

CPTP noise before the ideal BSM reduction and after message-dependent correction.
Noise location is explicit: pre channels act on the input of the ideal instrument.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `CPTP.positive`
- `CPTP.trace`
- `CPTP.map_add`
- `CPTP.map_smul`
- `CPTP.map_sum`
- `identity_map`
- `CPTP.cp`
- `composite_kraus_weighted`
- `noisy_micro_kraus`
- `noisy_micro_cp`
- `post_noise_trace_invariant`
- `noisy_reported_cp`
- `noisy_reject_cp`
- `noisy_outcome_cp`
- `noisy_outcome_trace`
- `noisy_outcome_positive`
- `noisy_total_trace`
- `noisy_probability`
- `noisy_null_iff`
- `ideal_noise_refinement`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

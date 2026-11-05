---
id: QuantumNoiseTransport
language: en
section: quantum-physics
source: Verification/QuantumNoiseTransport.lean
source_sha256: 7438a20cc4e296e41b7fbb49672db874359fce8dddab1a8fb70ad97f6710aec9
novelty: not-assessed
status: reviewed
---

# QuantumNoiseTransport

[Section](README.md) · [Lean source](../../Verification/QuantumNoiseTransport.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Exact transport of a CPTP channel through a unitary prefix. The transported
channel generally differs from the original; equality requires covariance.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `unitary_channel_map`
- `pullback_map`
- `slide_channel`
- `slide_branch`
- `pullback_eq_of_covariant`
- `central_pullback_operator`
- `central_pullback_map`
- `central_depolarizing_transport`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

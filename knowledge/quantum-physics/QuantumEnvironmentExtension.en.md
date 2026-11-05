---
id: QuantumEnvironmentExtension
language: en
section: quantum-physics
source: Verification/QuantumEnvironmentExtension.lean
source_sha256: 7067cacd7cf077fdf7d482b1da378e073f4d5b1798119583924118880300561e
novelty: not-assessed
status: reviewed
---

# QuantumEnvironmentExtension

[Section](README.md) · [Lean source](../../Verification/QuantumEnvironmentExtension.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Rectangular system operators extended by an untouched finite environment.
Branchwise environment elimination is an algebraic partial-trace identity.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `extend_adjoint`
- `extend_mul`
- `extend_one`
- `select_extend`
- `extend_insert`
- `trace_environment_sandwich`
- `trace_environment_sum`
- `trace_environment_smul`
- `branch_partial_trace`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

---
id: QuantumPersistentEnvironment
language: en
section: quantum-physics
source: Verification/QuantumPersistentEnvironment.lean
source_sha256: 93159a411e4c1aae485a89e37b2ee3f85dca6b2ce723e21a198a22e0a75c1529
novelty: not-assessed
status: reviewed
---

# QuantumPersistentEnvironment

[Section](README.md) · [Lean source](../../Verification/QuantumPersistentEnvironment.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

A finite environment retained throughout a joint circuit. Preparation and
partial trace are explicit matrices; the resulting system channel is CPTP for a
fixed initial environment basis state. Resetting after each stage is a distinct model.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `insert_isometry`
- `selectors_complete`
- `selector_sandwich`
- `trace_environment_family`
- `trace_environment_trace`
- `trace_environment_positive`
- `prepare_entry`
- `trace_environment_prepare`
- `prepare_positive`
- `prepare_trace`
- `reduced_map`
- `persistent_map`
- `reset_run_nil`
- `reset_run_cons`
- `joint_run_fresh`
- `persistent_equals_reset_of_fresh`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

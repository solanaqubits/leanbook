---
id: QuantumMemoryCounterexample
language: en
section: quantum-physics
source: Verification/QuantumMemoryCounterexample.lean
source_sha256: 09e35a06ead521efc7f9e9d33c906b786e2b7aec25954e8649e739b154d6a8c7
novelty: not-assessed
status: reviewed
---

# QuantumMemoryCounterexample

[Section](README.md) · [Lean source](../../Verification/QuantumMemoryCounterexample.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

A retained one-qubit memory restores coherence after two CNOT collisions.
Fresh-environment composition dephases instead. No map of the first system
marginal alone can reproduce both final coherent states.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `run_one_collision`
- `cnot_twice`
- `run_two_collisions`
- `collision_reduced_map`
- `persistent_once`
- `persistent_twice`
- `reset_collision_map`
- `dephase_idempotent`
- `reset_twice`
- `coherent_positive`
- `coherent_trace`
- `coherent_offdiagonal`
- `dephase_coherent`
- `coherent_states_distinct`
- `first_marginals_equal`
- `retained_and_reset_differ`
- `no_system_only_intermediate_map`
- `collision_not_fresh`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

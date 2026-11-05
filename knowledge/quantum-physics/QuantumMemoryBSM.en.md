---
id: QuantumMemoryBSM
language: en
section: quantum-physics
source: Verification/QuantumMemoryBSM.lean
source_sha256: d646314ca92f23618b7a26271938a572bf2ee5862f59958a7ab3ef22437a3a02
novelty: not-assessed
status: reviewed
---

# QuantumMemoryBSM

[Section](README.md) · [Lean source](../../Verification/QuantumMemoryBSM.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Direct Bell instrumentation with a retained environment across internal gates.
Environment elimination is performed branchwise, after joint evolution and readout.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `path_reduction_bridge`
- `path_branch_bridge`
- `micro_partial_trace`
- `reject_partial_trace`
- `outcome_partial_trace`
- `micro_bridge`
- `reject_bridge`
- `outcome_bridge`
- `outcome_noisy_bridge`
- `outcome_cp`
- `total_trace`
- `joint_run_refinement`
- `outcome_positive`
- `outcome_zero_iff`
- `joint_total_trace`
- `memory_ideal`
- `memory_run`
- `memory_outcome_bridge`
- `accepted_bridge`
- `memory_no_noise`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

---
id: QuantumMixedMemoryBSM
language: en
section: quantum-physics
source: Verification/QuantumMixedMemoryBSM.lean
source_sha256: 1cb066ec35a64002336a065182c26bc3130ed17b57c15ebb70a2a16c3190db5c
novelty: not-assessed
status: reviewed
---

# QuantumMixedMemoryBSM

[Section](README.md) · [Lean source](../../Verification/QuantumMixedMemoryBSM.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Direct Bell instrumentation with a retained environment across internal gates.
Environment elimination is performed branchwise, after joint evolution and readout.

The environment is prepared once in an arbitrary fixed mixed state and retained through the joint circuit. Direct rectangular branch operators are proved equal to partial traces of joint branches. Under the explicit ideal-circuit-factorization hypothesis, they refine the existing five-outcome BSM instrument after the effective input channel. CP, trace balance and null-branch equivalence are preserved. Pure-basis and unused-environment limits recover earlier contracts.

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
- `pure_basis_outcome`
- `outcome_density_extensionality`
- `memory_outcome_bridge`
- `memory_no_noise`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

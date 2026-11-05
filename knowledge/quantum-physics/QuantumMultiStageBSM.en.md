---
id: QuantumMultiStageBSM
language: en
section: quantum-physics
source: Verification/QuantumMultiStageBSM.lean
source_sha256: 4b14d48c2d7f2163f6b8e90522d0ae112b5cbba48be104711d3b91fbdc1eaf00
novelty: not-assessed
status: reviewed
---

# QuantumMultiStageBSM

[Section](README.md) · [Lean source](../../Verification/QuantumMultiStageBSM.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Direct multi-stage Bell instrumentation and its ordered effective input channel.
The concrete analyzer has independent noise after CNOT and after Hadamard.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `path_reduction_bridge`
- `path_branch_bridge`
- `micro_bridge`
- `reject_bridge`
- `outcome_bridge`
- `outcome_noisy_bridge`
- `outcome_cp`
- `total_trace`
- `h_gate_matrix`
- `bsm_ideal`
- `bsm_run`
- `bsm_outcome_bridge`
- `bsm_effective_order`
- `depolarizing_compose`
- `central_composition`
- `two_depolarizing_effective`
- `accepted_bridge`
- `two_noise_local_visibility`
- `qubit_zero_valid`
- `reset_order_changes_probability`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

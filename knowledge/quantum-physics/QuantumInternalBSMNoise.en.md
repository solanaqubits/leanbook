---
id: QuantumInternalBSMNoise
language: en
section: quantum-physics
source: Verification/QuantumInternalBSMNoise.lean
source_sha256: 753110d39c0ef7f5811b80734f99077e4131f1fded3e5dbc8d5908daaaf32bce
novelty: not-assessed
status: reviewed
---

# QuantumInternalBSMNoise

[Section](README.md) · [Lean source](../../Verification/QuantumInternalBSMNoise.lean) ·
[Publication and verification scope](../../docs/quantum-v4.20.md)

Noise at an explicit cut of the CNOT/H Bell analyzer. Computational readout
is defined directly; agreement with the pre-noise instrument is a theorem.

The statements below are contracts of the finite mathematical model. Their hypotheses, index types, normalization conditions and noise location are part of each theorem; they are not inferred properties of a physical device.

## Checked declarations

- `cnot_adjoint`
- `cnot_squared`
- `computational_analysis_reduction`
- `cut_reduction`
- `internal_reduction_transport`
- `internal_branch_transport`
- `internal_micro_refinement`
- `internal_reject_refinement`
- `internal_outcome_refinement`
- `internal_outcome_noisy_bridge`
- `internal_outcome_cp`
- `internal_total_trace`
- `internal_depolarizing_outcome`
- `internal_accepted_refinement`
- `internal_depolarizing_accepted`
- `internal_local_visibility`
- `flip_control_unitary`
- `flip_control_adjoint`
- `cnot_transports_control_flip_to_both`
- `naive_noise_relocation_changes_born_probability`
- `verification_suite`

## Evidence and limits

The publication verifies this source tree independently of the private development tree.
See the linked scope record for build, audit and regression commands and results.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the axiom audit.
No claim of experimental validation, hardware calibration or circuit-level fault-tolerance
threshold follows from these statements. Novelty has not been assessed.

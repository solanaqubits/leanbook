---
id: QuantumTensorStageEnvironment
language: en
section: quantum-physics
source: Verification/QuantumTensorStageEnvironment.lean
source_sha256: 3277a5d6d56dde0714a5782775b05eeca77ff7fd8828e7575f0a503c48cb1870
novelty: not-assessed
status: reviewed
---

# QuantumTensorStageEnvironment

[Section](README.md) · [Lean source](../../Verification/QuantumTensorStageEnvironment.lean) ·
[Scope](../../docs/quantum-v4.23.md)

Pairs each system stage with an independent environment stage. Both its unitary
and its CPTP noise may vary at every step, including different finite Kraus-label
types. For arbitrary joint matrices, partial trace commutes with the chronological
run and all five reduced instrument outcomes depend only on the initial system
marginal. Environment channels need trace preservation, not unitality.

The identity-environment specialization equates actions, not Stage structures:
labels times Unit and labels are different dependent representations. Correlations
may remain in the full joint state. No PSD, factorization, perfect-readout or
ideal-analyzer premise is needed for the algebraic marginal-reduction theorem.

## Theorems

- [`QuantumTensorStageEnvironment.traceEnvironment_tensorGate`](../../Verification/QuantumTensorStageEnvironment.lean#L36)
- [`QuantumTensorStageEnvironment.traceEnvironment_tensorStage_step`](../../Verification/QuantumTensorStageEnvironment.lean#L43)
- [`QuantumTensorStageEnvironment.tensorCPTP_identity_map`](../../Verification/QuantumTensorStageEnvironment.lean#L53)
- [`QuantumTensorStageEnvironment.tensorStage_identity_step_eq_extendStage`](../../Verification/QuantumTensorStageEnvironment.lean#L58)
- [`QuantumTensorStageEnvironment.traceEnvironment_run_tensorStages`](../../Verification/QuantumTensorStageEnvironment.lean#L70)
- [`QuantumTensorStageEnvironment.tensorStages_outcome_marginal_reduction`](../../Verification/QuantumTensorStageEnvironment.lean#L81)
- [`QuantumTensorStageEnvironment.tensorStages_reducedJointOutcome`](../../Verification/QuantumTensorStageEnvironment.lean#L94)
- [`QuantumTensorStageEnvironment.tensorStages_identity_run`](../../Verification/QuantumTensorStageEnvironment.lean#L103)
- [`QuantumTensorStageEnvironment.verification_suite`](../../Verification/QuantumTensorStageEnvironment.lean#L122)

## Limits

Sufficient conditions and explicit examples, not a classification of all interactions.
One instrument cycle; no adaptive process tensors or hardware characterization.
No scientific-priority claim. See the candidate report for exact validation scope.

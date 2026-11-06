---
id: QuantumPostBSMEnvironment
language: en
section: quantum-physics
source: Verification/QuantumPostBSMEnvironment.lean
source_sha256: 92f2929797c1145283e3e4d8332e42ed1ea2c8bbd6e8509140ce3a7307bf0314
novelty: not-assessed
status: reviewed
---

# QuantumPostBSMEnvironment

[Section](README.md) · [Lean source](../../Verification/QuantumPostBSMEnvironment.lean) ·
[Scope](../../docs/quantum-v4.23.md)

Constructs a CNOT from central system qubit B to a two-dimensional environment,
placed after the preceding stages and immediately before computational BC readout.
The matrix has no Kronecker factorization, even into unrestricted complex matrices.
Nevertheless all five reduced outcomes are unchanged for every joint input,
Readout and preceding joint stage list. On an extended ideal analyzer this yields
a function of the initial system marginal.

Cancellation uses computationalReduction, not branchOperator (which already
includes the Bell analyzer). A fixed measurement branch has the same B label
on both sides, so the environment-index sum is merely permuted. The argument
covers off-diagonal AD coherences and needs no PSD premise.

A normalized PSD pure input at the measurement cut changes under this interaction.
The resulting ket has no system/environment product factorization. This is a
pure-state tensor-factor obstruction, not a general mixed-state separability API.

## Theorems

- [`QuantumPostBSMEnvironment.flipBE_involutive`](../../Verification/QuantumPostBSMEnvironment.lean#L24)
- [`QuantumPostBSMEnvironment.flipBE_eq_iff`](../../Verification/QuantumPostBSMEnvironment.lean#L28)
- [`QuantumPostBSMEnvironment.post_left`](../../Verification/QuantumPostBSMEnvironment.lean#L36)
- [`QuantumPostBSMEnvironment.post_right`](../../Verification/QuantumPostBSMEnvironment.lean#L40)
- [`QuantumPostBSMEnvironment.post_adjoint`](../../Verification/QuantumPostBSMEnvironment.lean#L44)
- [`QuantumPostBSMEnvironment.post_squared`](../../Verification/QuantumPostBSMEnvironment.lean#L50)
- [`QuantumPostBSMEnvironment.post_channel_entry`](../../Verification/QuantumPostBSMEnvironment.lean#L58)
- [`QuantumPostBSMEnvironment.postBSMCnotBE_not_kronecker_product`](../../Verification/QuantumPostBSMEnvironment.lean#L65)
- [`QuantumPostBSMEnvironment.computational_sandwich_entry`](../../Verification/QuantumPostBSMEnvironment.lean#L85)
- [`QuantumPostBSMEnvironment.computational_reduction_post_cancel`](../../Verification/QuantumPostBSMEnvironment.lean#L94)
- [`QuantumPostBSMEnvironment.corrected_computational_post_cancel`](../../Verification/QuantumPostBSMEnvironment.lean#L105)
- [`QuantumPostBSMEnvironment.select_branch_postBSMCnotBE_cancel`](../../Verification/QuantumPostBSMEnvironment.lean#L116)
- [`QuantumPostBSMEnvironment.run_postStage`](../../Verification/QuantumPostBSMEnvironment.lean#L129)
- [`QuantumPostBSMEnvironment.post_interaction_outcome_invariant`](../../Verification/QuantumPostBSMEnvironment.lean#L138)
- [`QuantumPostBSMEnvironment.postBSMCnotBE_preserves_all_reducedJointOutcomes`](../../Verification/QuantumPostBSMEnvironment.lean#L156)
- [`QuantumPostBSMEnvironment.probeState_positive`](../../Verification/QuantumPostBSMEnvironment.lean#L171)
- [`QuantumPostBSMEnvironment.probeState_trace_one`](../../Verification/QuantumPostBSMEnvironment.lean#L174)
- [`QuantumPostBSMEnvironment.probeState_coupled_pure`](../../Verification/QuantumPostBSMEnvironment.lean#L178)
- [`QuantumPostBSMEnvironment.coupledKet_not_product`](../../Verification/QuantumPostBSMEnvironment.lean#L185)
- [`QuantumPostBSMEnvironment.post_changes_joint_probe`](../../Verification/QuantumPostBSMEnvironment.lean#L210)
- [`QuantumPostBSMEnvironment.verification_suite`](../../Verification/QuantumPostBSMEnvironment.lean#L227)

## Limits

Sufficient conditions and explicit examples, not a classification of all interactions.
One instrument cycle; no adaptive process tensors or hardware characterization.
No scientific-priority claim. See the candidate report for exact validation scope.

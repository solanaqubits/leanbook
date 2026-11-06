---
id: QuantumAdaptiveWernerCascade
language: en
section: quantum-physics
source: Verification/QuantumAdaptiveWernerCascade.lean
source_sha256: ad1c5661caf1e91b72cb5d0236d59ca2ebb16f09d9d8968b03471ca1c89bda5a
novelty: not-assessed
status: reviewed
---

# Quantum v4.28: adaptive Werner cascade with detector loss

Local additive candidate over `3cdac4021bf5c9b574116c19dec2461125b9e31c`.
The published Leanbook 1.0.0 tag is unchanged.

The first result proves each individual corrected Bell sandwich, then includes
central BC depolarization, full-pair AD post depolarization, and faithful delivery
with detector efficiencies in [0,1]. It does not infer individual branches from
an aggregated equality. Each initial Werner pair is independent of the other
and of the first memory.

The actual v4.26 Cascade chooses second-round noise, a fresh Werner pair and
fresh independent memory by the delivered first message. Each successful history
has weight eta1(r)*eta2(r,t)/16. Summing gives q(r) and total success P. The exact
matrix sum, trace P, zero matrix at P=0 and normalized affine Werner matrix at
P>0 are proved. Conditional visibility is bounded in [0,1]. Selected branches
also have an explicit conditional matrix formula. The target-overlap lemma
connects these matrices to the scalar fidelity comparison.

A positively weighted branch above the weighted mean beats the aggregate fidelity
but cannot exceed the first-round fidelity. This is not global policy optimization
or entanglement distillation. Arbitrary label confusion is outside the Werner
specialization; the general underlying instrument retains that capability.

The affine `wernerMatrix` accepts real scalars algebraically; physical operator
channels use bounded `Visibility`. The conditional bound is separately proved.
First memory is discarded; no persistent multi-round environmental correlations
or process tensor model are claimed.

Validation scope is gamma: strict module/import closure, incremental registry
build and targeted regressions. See the verification JSON for actual results;
these do not constitute a new full-library test discovery or clean build.

## Theorems

- [`QuantumAdaptiveWernerCascade.faithful_sandwich`](../../Verification/QuantumAdaptiveWernerCascade.lean#L30)
- [`QuantumAdaptiveWernerCascade.faithful_mixed_sandwich`](../../Verification/QuantumAdaptiveWernerCascade.lean#L42)
- [`QuantumAdaptiveWernerCascade.lossy_reported`](../../Verification/QuantumAdaptiveWernerCascade.lean#L47)
- [`QuantumAdaptiveWernerCascade.ideal_isotropic`](../../Verification/QuantumAdaptiveWernerCascade.lean#L57)
- [`QuantumAdaptiveWernerCascade.wernerRound_lossy_single_branch_map`](../../Verification/QuantumAdaptiveWernerCascade.lean#L63)
- [`QuantumAdaptiveWernerCascade.adaptive_branch_matrix`](../../Verification/QuantumAdaptiveWernerCascade.lean#L124)
- [`QuantumAdaptiveWernerCascade.branch_weight_nonnegative`](../../Verification/QuantumAdaptiveWernerCascade.lean#L158)
- [`QuantumAdaptiveWernerCascade.adaptive_success_matrix`](../../Verification/QuantumAdaptiveWernerCascade.lean#L163)
- [`QuantumAdaptiveWernerCascade.adaptive_success_trace`](../../Verification/QuantumAdaptiveWernerCascade.lean#L181)
- [`QuantumAdaptiveWernerCascade.isotropic_affine`](../../Verification/QuantumAdaptiveWernerCascade.lean#L197)
- [`QuantumAdaptiveWernerCascade.affine_weighted_sum`](../../Verification/QuantumAdaptiveWernerCascade.lean#L204)
- [`QuantumAdaptiveWernerCascade.affine_conditional`](../../Verification/QuantumAdaptiveWernerCascade.lean#L211)
- [`QuantumAdaptiveWernerCascade.zero_weight_sum`](../../Verification/QuantumAdaptiveWernerCascade.lean#L219)
- [`QuantumAdaptiveWernerCascade.positive_branch_total`](../../Verification/QuantumAdaptiveWernerCascade.lean#L228)
- [`QuantumAdaptiveWernerCascade.weightedAlpha_bounds`](../../Verification/QuantumAdaptiveWernerCascade.lean#L234)
- [`QuantumAdaptiveWernerCascade.heralded_branch_comparison_weighted`](../../Verification/QuantumAdaptiveWernerCascade.lean#L245)
- [`QuantumAdaptiveWernerCascade.output_visibility_value`](../../Verification/QuantumAdaptiveWernerCascade.lean#L261)
- [`QuantumAdaptiveWernerCascade.adaptive_success_zero`](../../Verification/QuantumAdaptiveWernerCascade.lean#L273)
- [`QuantumAdaptiveWernerCascade.adaptive_success_conditional`](../../Verification/QuantumAdaptiveWernerCascade.lean#L280)
- [`QuantumAdaptiveWernerCascade.conditional_visibility_bounds`](../../Verification/QuantumAdaptiveWernerCascade.lean#L294)
- [`QuantumAdaptiveWernerCascade.perfect_branch_weight`](../../Verification/QuantumAdaptiveWernerCascade.lean#L310)
- [`QuantumAdaptiveWernerCascade.perfect_total_probability`](../../Verification/QuantumAdaptiveWernerCascade.lean#L316)
- [`QuantumAdaptiveWernerCascade.perfect_weighted_mean`](../../Verification/QuantumAdaptiveWernerCascade.lean#L323)
- [`QuantumAdaptiveWernerCascade.closed_first_probability`](../../Verification/QuantumAdaptiveWernerCascade.lean#L329)
- [`QuantumAdaptiveWernerCascade.closed_second_probability`](../../Verification/QuantumAdaptiveWernerCascade.lean#L333)
- [`QuantumAdaptiveWernerCascade.wernerMatrix_fidelity`](../../Verification/QuantumAdaptiveWernerCascade.lean#L339)
- [`QuantumAdaptiveWernerCascade.adaptive_selected_matrix`](../../Verification/QuantumAdaptiveWernerCascade.lean#L345)
- [`QuantumAdaptiveWernerCascade.adaptive_selected_conditional`](../../Verification/QuantumAdaptiveWernerCascade.lean#L361)
- [`QuantumAdaptiveWernerCascade.verification_suite`](../../Verification/QuantumAdaptiveWernerCascade.lean#L387)

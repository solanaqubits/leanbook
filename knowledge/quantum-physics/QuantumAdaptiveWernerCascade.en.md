---
id: QuantumAdaptiveWernerCascade
language: en
section: quantum-physics
source: Verification/QuantumAdaptiveWernerCascade.lean
source_sha256: 4c0dd93bcb6687f8705b553ec18566e0891de18c4f33abcda921613e456b77bc
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

- [`QuantumAdaptiveWernerCascade.faithful_sandwich`](../../Verification/QuantumAdaptiveWernerCascade.lean#L35)
- [`QuantumAdaptiveWernerCascade.faithful_mixed_sandwich`](../../Verification/QuantumAdaptiveWernerCascade.lean#L47)
- [`QuantumAdaptiveWernerCascade.lossy_reported`](../../Verification/QuantumAdaptiveWernerCascade.lean#L52)
- [`QuantumAdaptiveWernerCascade.ideal_isotropic`](../../Verification/QuantumAdaptiveWernerCascade.lean#L62)
- [`QuantumAdaptiveWernerCascade.wernerRound_lossy_single_branch_map`](../../Verification/QuantumAdaptiveWernerCascade.lean#L68)
- [`QuantumAdaptiveWernerCascade.adaptive_branch_matrix`](../../Verification/QuantumAdaptiveWernerCascade.lean#L129)
- [`QuantumAdaptiveWernerCascade.branch_weight_nonnegative`](../../Verification/QuantumAdaptiveWernerCascade.lean#L163)
- [`QuantumAdaptiveWernerCascade.adaptive_success_matrix`](../../Verification/QuantumAdaptiveWernerCascade.lean#L168)
- [`QuantumAdaptiveWernerCascade.adaptive_success_trace`](../../Verification/QuantumAdaptiveWernerCascade.lean#L186)
- [`QuantumAdaptiveWernerCascade.isotropic_affine`](../../Verification/QuantumAdaptiveWernerCascade.lean#L202)
- [`QuantumAdaptiveWernerCascade.affine_weighted_sum`](../../Verification/QuantumAdaptiveWernerCascade.lean#L209)
- [`QuantumAdaptiveWernerCascade.affine_conditional`](../../Verification/QuantumAdaptiveWernerCascade.lean#L216)
- [`QuantumAdaptiveWernerCascade.zero_weight_sum`](../../Verification/QuantumAdaptiveWernerCascade.lean#L224)
- [`QuantumAdaptiveWernerCascade.positive_branch_total`](../../Verification/QuantumAdaptiveWernerCascade.lean#L233)
- [`QuantumAdaptiveWernerCascade.weightedAlpha_bounds`](../../Verification/QuantumAdaptiveWernerCascade.lean#L239)
- [`QuantumAdaptiveWernerCascade.heralded_branch_comparison_weighted`](../../Verification/QuantumAdaptiveWernerCascade.lean#L250)
- [`QuantumAdaptiveWernerCascade.output_visibility_value`](../../Verification/QuantumAdaptiveWernerCascade.lean#L266)
- [`QuantumAdaptiveWernerCascade.adaptive_success_zero`](../../Verification/QuantumAdaptiveWernerCascade.lean#L278)
- [`QuantumAdaptiveWernerCascade.adaptive_success_conditional`](../../Verification/QuantumAdaptiveWernerCascade.lean#L285)
- [`QuantumAdaptiveWernerCascade.conditional_visibility_bounds`](../../Verification/QuantumAdaptiveWernerCascade.lean#L299)
- [`QuantumAdaptiveWernerCascade.perfect_branch_weight`](../../Verification/QuantumAdaptiveWernerCascade.lean#L315)
- [`QuantumAdaptiveWernerCascade.perfect_total_probability`](../../Verification/QuantumAdaptiveWernerCascade.lean#L321)
- [`QuantumAdaptiveWernerCascade.perfect_weighted_mean`](../../Verification/QuantumAdaptiveWernerCascade.lean#L328)
- [`QuantumAdaptiveWernerCascade.closed_first_probability`](../../Verification/QuantumAdaptiveWernerCascade.lean#L334)
- [`QuantumAdaptiveWernerCascade.closed_second_probability`](../../Verification/QuantumAdaptiveWernerCascade.lean#L338)
- [`QuantumAdaptiveWernerCascade.wernerMatrix_fidelity`](../../Verification/QuantumAdaptiveWernerCascade.lean#L344)
- [`QuantumAdaptiveWernerCascade.adaptive_selected_matrix`](../../Verification/QuantumAdaptiveWernerCascade.lean#L350)
- [`QuantumAdaptiveWernerCascade.adaptive_selected_conditional`](../../Verification/QuantumAdaptiveWernerCascade.lean#L366)
- [`QuantumAdaptiveWernerCascade.verification_suite`](../../Verification/QuantumAdaptiveWernerCascade.lean#L392)

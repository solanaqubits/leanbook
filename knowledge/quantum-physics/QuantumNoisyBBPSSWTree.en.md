---
id: QuantumNoisyBBPSSWTree
language: en
section: quantum-physics
source: Verification/QuantumNoisyBBPSSWTree.lean
source_sha256: 1bded450afc7fe44a11380f52a43869bc436460fc0d69fce0739e3d75c48dd0e
novelty: not-assessed
status: reviewed
---

# QuantumNoisyBBPSSWTree

[Section](README.md) · [Scope](../../docs/quantum-v4.37.md) ·
[Source](../../Verification/QuantumNoisyBBPSSWTree.lean)

The unnormalized binary tree applies noisyPurified to two independent subtrees
at every internal node. Noise is post-depolarization of the whole retained pair,
not a noisy CNOT or input-pair channel. The matrix identity holds for every real
initial Werner parameter; physical density claims require 0<=F0<=1 and the
operator quality parameter is Visibility.

At level n, F_n=noisyOrbit gamma F0 n and D_n=p_n*werner(F_n). The full-tree
weight satisfies p_0=1 and p_(n+1)=p_n^2*P(F_n). Its closed form is the product
over j<n of P(F_j)^(2^(n-1-j)); it is not the single-path product. Weights are
strictly positive for arbitrary real scalar gamma,F0, and bounded above by one
on the physical domain. Matrix trace equals p_n. Conditional normalization
produces a PSD matrix of trace one. The tree consumes 2^n independent input pairs.

swapThenNoisyTree starts from the actual pairSwap instrument, whose ideal
corrected outcome aggregate on equal isotropic inputs has unit trace and Werner
fidelity swapFidelity(w). Its noisy tree has the same matrix refinement and
consumes 2^(n+1) elementary pairs across two spatial segments. Purification depth
n is not a spatial repeater level.

For 0<w<1 and criticalGamma<gamma<1, some finite depth strictly exceeds the
elementary segment fidelity exactly when lowerWindowBound(gamma)<swapFidelity(w)
and elemFidelity(w)<upperWindowCeiling(gamma). Necessity uses stationary endpoints,
decreasing-orbit bounds and the no-overshoot window invariant. Sufficiency uses
the existing Tendsto theorem and an open neighborhood of the ceiling.

At gamma=1 the matrix and weights reduce to the ideal tree. At gamma=0 the
normalized matrix equals werner(1/4) at every positive depth, including real
nonphysical input parameters as an algebraic identity. At F0=1/4 the weight is
(1/2)^(2^n-1). At gamma=19/20, w=4/5 admits a finite recovery depth; w=9/10 stays
strictly below its initial segment fidelity at every depth, so equality is also
impossible in that witness. No minimal noisy recovery depth is asserted.

The nonlinear diagonal preparation encodes independent resources, not cloning.
This work does not give a retry policy, expected resource yield, variable quality,
convergence rate or a spatially nested noisy repeater.

## Theorems

- [`QuantumNoisyBBPSSWTree.noisyTreeProbability_pos`](../../Verification/QuantumNoisyBBPSSWTree.lean#L31)
- [`QuantumNoisyBBPSSWTree.noisyTreeProbability_closed_form`](../../Verification/QuantumNoisyBBPSSWTree.lean#L37)
- [`QuantumNoisyBBPSSWTree.noisyTreeProbability_two`](../../Verification/QuantumNoisyBBPSSWTree.lean#L55)
- [`QuantumNoisyBBPSSWTree.noisyTreeProbability_le_one`](../../Verification/QuantumNoisyBBPSSWTree.lean#L60)
- [`QuantumNoisyBBPSSWTree.noisyTreeMatrix_eq_werner`](../../Verification/QuantumNoisyBBPSSWTree.lean#L70)
- [`QuantumNoisyBBPSSWTree.noisyTreeMatrix_trace`](../../Verification/QuantumNoisyBBPSSWTree.lean#L81)
- [`QuantumNoisyBBPSSWTree.noisyTreeMatrix_posSemidef`](../../Verification/QuantumNoisyBBPSSWTree.lean#L85)
- [`QuantumNoisyBBPSSWTree.noisyTreeMatrix_conditional`](../../Verification/QuantumNoisyBBPSSWTree.lean#L91)
- [`QuantumNoisyBBPSSWTree.noisyTreeMatrix_conditional_density`](../../Verification/QuantumNoisyBBPSSWTree.lean#L98)
- [`QuantumNoisyBBPSSWTree.noisyTreeInputPairs_eq`](../../Verification/QuantumNoisyBBPSSWTree.lean#L112)
- [`QuantumNoisyBBPSSWTree.swapThenNoisyTree_eq_noisyTreeMatrix`](../../Verification/QuantumNoisyBBPSSWTree.lean#L122)
- [`QuantumNoisyBBPSSWTree.swapThenNoisyTree_refinement`](../../Verification/QuantumNoisyBBPSSWTree.lean#L132)
- [`QuantumNoisyBBPSSWTree.swapThenNoisyTree_conditional`](../../Verification/QuantumNoisyBBPSSWTree.lean#L138)
- [`QuantumNoisyBBPSSWTree.swapThenNoisyTreeRawPairs_eq`](../../Verification/QuantumNoisyBBPSSWTree.lean#L145)
- [`QuantumNoisyBBPSSWTree.noisyOrbit_le_initial_below_lower`](../../Verification/QuantumNoisyBBPSSWTree.lean#L149)
- [`QuantumNoisyBBPSSWTree.noisyOrbit_le_initial_above_ceiling`](../../Verification/QuantumNoisyBBPSSWTree.lean#L158)
- [`QuantumNoisyBBPSSWTree.exists_noisy_depth_exceeding_elemFidelity_iff`](../../Verification/QuantumNoisyBBPSSWTree.lean#L168)
- [`QuantumNoisyBBPSSWTree.noisyOrbit_unit`](../../Verification/QuantumNoisyBBPSSWTree.lean#L202)
- [`QuantumNoisyBBPSSWTree.noisyTreeProbability_unit`](../../Verification/QuantumNoisyBBPSSWTree.lean#L207)
- [`QuantumNoisyBBPSSWTree.noisyTreeMatrix_unit`](../../Verification/QuantumNoisyBBPSSWTree.lean#L213)
- [`QuantumNoisyBBPSSWTree.noisyTreeMatrix_zero_conditional`](../../Verification/QuantumNoisyBBPSSWTree.lean#L219)
- [`QuantumNoisyBBPSSWTree.noisyTreeProbability_quarter`](../../Verification/QuantumNoisyBBPSSWTree.lean#L228)
- [`QuantumNoisyBBPSSWTree.nineteen_twentieths_four_fifths_recovery_possible`](../../Verification/QuantumNoisyBBPSSWTree.lean#L241)
- [`QuantumNoisyBBPSSWTree.nineteen_twentieths_nine_tenths_below_elem`](../../Verification/QuantumNoisyBBPSSWTree.lean#L256)
- [`QuantumNoisyBBPSSWTree.nineteen_twentieths_nine_tenths_recovery_impossible`](../../Verification/QuantumNoisyBBPSSWTree.lean#L275)
- [`QuantumNoisyBBPSSWTree.verification_suite`](../../Verification/QuantumNoisyBBPSSWTree.lean#L288)

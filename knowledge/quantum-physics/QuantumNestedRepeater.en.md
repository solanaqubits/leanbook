---
id: QuantumNestedRepeater
language: en
section: quantum-physics
source: Verification/QuantumNestedRepeater.lean
source_sha256: b29c1499c24a9730a9cb5418c919badb35ecef4d539d9e4ec249ccde6a443981
novelty: not-assessed
status: reviewed
---

# QuantumNestedRepeater

[Section](README.md) · [Scope](../../docs/quantum-v4.33.md) ·
[Source](../../Verification/QuantumNestedRepeater.lean)

The one-round repeater visibility tends to zero for every initial Visibility below
one; fidelity tends to one quarter. Both exact step factorizations are proved.
A local benefit over pure swapping does not imply a global comparison: initial
visibility 3/5 benefits at level one but loses to pure swapping at level two.

A nested level performs one ideal swap followed by a binary BBPSSW tree of depth m.
Each level consumes B=2^(m+1) independent child resources. The general purifiedTree
is homogeneous of degree 2^m, and agrees with treeMatrix on Werner inputs.
The unnormalized recursive output is exactly p_k times isotropic(w_k), where
w_(k+1)=(4*R^m((1+3*w_k^2)/4)-1)/3 and
p_(k+1)=p_k^B*treeProbability(swapFidelity(w_k),m).
Its weight is positive and at most one, equals the trace, and normalization yields
a PSD state of trace one with the derived target fidelity.

Strict monotonicity of recurrence on [1/4,1] and of the nested visibility map on
[0,1] propagates a first-step gain to strict growth at every finite level. Initial
visibility 4/5 with m=4 has such a gain and exceeds its initial fidelity 17/20 at
every positive level while remaining strictly below one. No convergence to one
for nested orbits is claimed. The m=0 specialization recovers pure swapping and
unit success weight; m=1 recovers v4.32 matrices, visibility and weights.
Spatial span is 2^k segments; raw pair count is 2^((m+1)*k), or 2^(m*k) copies per
segment. These are all-success conditional constructions, not expected yield,
rate, retries, memory lifetimes, arbitrary correlated inputs or cloning channels.

## Theorems

- [`QuantumNestedRepeater.nodeVisibilityValue_loss_factorization`](../../Verification/QuantumNestedRepeater.lean#L20)
- [`QuantumNestedRepeater.nodeVisibilityValue_sub_sq_factorization`](../../Verification/QuantumNestedRepeater.lean#L27)
- [`QuantumNestedRepeater.nodeVisibilityValue_between_sq_and_self`](../../Verification/QuantumNestedRepeater.lean#L33)
- [`QuantumNestedRepeater.three_fifths_two_step_swap_reversal`](../../Verification/QuantumNestedRepeater.lean#L44)
- [`QuantumNestedRepeater.nodeVisibilityValue_fixed_iff`](../../Verification/QuantumNestedRepeater.lean#L52)
- [`QuantumNestedRepeater.continuous_nodeVisibilityValue`](../../Verification/QuantumNestedRepeater.lean#L65)
- [`QuantumNestedRepeater.visibilityAt_tendsto_zero`](../../Verification/QuantumNestedRepeater.lean#L70)
- [`QuantumNestedRepeater.elemFidelity_visibilityAt_tendsto_quarter`](../../Verification/QuantumNestedRepeater.lean#L89)
- [`QuantumNestedRepeater.recurrence_strictMonoOn`](../../Verification/QuantumNestedRepeater.lean#L96)
- [`QuantumNestedRepeater.recurrence_quarter_bounds`](../../Verification/QuantumNestedRepeater.lean#L111)
- [`QuantumNestedRepeater.fidelityOrbit_quarter_bounds`](../../Verification/QuantumNestedRepeater.lean#L120)
- [`QuantumNestedRepeater.fidelityOrbit_strictMonoOn`](../../Verification/QuantumNestedRepeater.lean#L126)
- [`QuantumNestedRepeater.nestedNodeVisibility_bounds`](../../Verification/QuantumNestedRepeater.lean#L140)
- [`QuantumNestedRepeater.nestedNodeVisibility_strictMonoOn`](../../Verification/QuantumNestedRepeater.lean#L158)
- [`QuantumNestedRepeater.nestedVisibilityAt_strictMono_of_first_step_gain`](../../Verification/QuantumNestedRepeater.lean#L174)
- [`QuantumNestedRepeater.nestedVisibilityAt_sustains_initial_quality`](../../Verification/QuantumNestedRepeater.lean#L186)
- [`QuantumNestedRepeater.fourFifths_depth_four_gain`](../../Verification/QuantumNestedRepeater.lean#L196)
- [`QuantumNestedRepeater.nestedRepeater_four_fifths_depth_four_sustains`](../../Verification/QuantumNestedRepeater.lean#L202)
- [`QuantumNestedRepeater.nestedVisibilityAt_lt_one_of_gain`](../../Verification/QuantumNestedRepeater.lean#L211)
- [`QuantumNestedRepeater.purifiedTree_smul`](../../Verification/QuantumNestedRepeater.lean#L222)
- [`QuantumNestedRepeater.purifiedTree_werner`](../../Verification/QuantumNestedRepeater.lean#L233)
- [`QuantumNestedRepeater.nestedNode_fidelity`](../../Verification/QuantumNestedRepeater.lean#L258)
- [`QuantumNestedRepeater.nestedRepeaterStep_smul`](../../Verification/QuantumNestedRepeater.lean#L263)
- [`QuantumNestedRepeater.nestedRepeaterStep_isotropic`](../../Verification/QuantumNestedRepeater.lean#L271)
- [`QuantumNestedRepeater.nestedNodeProbability_pos`](../../Verification/QuantumNestedRepeater.lean#L283)
- [`QuantumNestedRepeater.nestedNodeProbability_le_one`](../../Verification/QuantumNestedRepeater.lean#L286)
- [`QuantumNestedRepeater.nestedRepeaterProbability_pos`](../../Verification/QuantumNestedRepeater.lean#L293)
- [`QuantumNestedRepeater.nestedRepeaterProbability_le_one`](../../Verification/QuantumNestedRepeater.lean#L299)
- [`QuantumNestedRepeater.nestedRepeaterMatrix_refinement`](../../Verification/QuantumNestedRepeater.lean#L307)
- [`QuantumNestedRepeater.nestedRepeaterMatrix_positive`](../../Verification/QuantumNestedRepeater.lean#L317)
- [`QuantumNestedRepeater.nestedRepeaterMatrix_trace`](../../Verification/QuantumNestedRepeater.lean#L322)
- [`QuantumNestedRepeater.nestedRepeaterMatrix_conditional`](../../Verification/QuantumNestedRepeater.lean#L326)
- [`QuantumNestedRepeater.nestedRepeaterMatrix_conditional_density`](../../Verification/QuantumNestedRepeater.lean#L333)
- [`QuantumNestedRepeater.nestedRepeaterMatrix_conditional_fidelity`](../../Verification/QuantumNestedRepeater.lean#L340)
- [`QuantumNestedRepeater.nestedRawPairCount_eq`](../../Verification/QuantumNestedRepeater.lean#L346)
- [`QuantumNestedRepeater.nestedRawPairCount_per_segment`](../../Verification/QuantumNestedRepeater.lean#L349)
- [`QuantumNestedRepeater.nestedNodeVisibilityValue_zero`](../../Verification/QuantumNestedRepeater.lean#L356)
- [`QuantumNestedRepeater.nestedVisibilityAt_zero`](../../Verification/QuantumNestedRepeater.lean#L360)
- [`QuantumNestedRepeater.nestedRepeaterProbability_zero`](../../Verification/QuantumNestedRepeater.lean#L368)
- [`QuantumNestedRepeater.nestedRepeaterStep_one`](../../Verification/QuantumNestedRepeater.lean#L375)
- [`QuantumNestedRepeater.nestedRepeaterMatrix_one`](../../Verification/QuantumNestedRepeater.lean#L378)
- [`QuantumNestedRepeater.nestedNodeVisibilityValue_one`](../../Verification/QuantumNestedRepeater.lean#L384)
- [`QuantumNestedRepeater.nestedVisibilityAt_one`](../../Verification/QuantumNestedRepeater.lean#L391)
- [`QuantumNestedRepeater.nestedRepeaterProbability_one`](../../Verification/QuantumNestedRepeater.lean#L399)
- [`QuantumNestedRepeater.verification_suite`](../../Verification/QuantumNestedRepeater.lean#L414)

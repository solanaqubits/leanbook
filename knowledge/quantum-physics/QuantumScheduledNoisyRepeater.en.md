---
id: QuantumScheduledNoisyRepeater
language: en
section: quantum-physics
source: Verification/QuantumScheduledNoisyRepeater.lean
source_sha256: 0b48fd5cbbed7903963deca5b41d352661304761d976780c010d72e201906db4
novelty: not-assessed
status: reviewed
---

# QuantumScheduledNoisyRepeater

[Section](README.md) · [Scope](../../docs/quantum-v4.38.md) ·
[Source](../../Verification/QuantumScheduledNoisyRepeater.lean)

The chronological List.foldl accumulator stores the actual unnormalized matrix,
its full-tree success weight and physical Visibility. The step applies ideal
pairSwap followed by noisyGeneralTree at the scheduled depth. The constant quality
gamma post-depolarizes the retained pair at each BBPSSW node. No early normalization
or reconstruction of visibility from arbitrary matrices is used.

The proved accumulator invariant states D=p*isotropic(w) with 0<p<=1. Each level
raises its incoming weight to 2^(m+1) and multiplies by noisyTreeProbability along
the noisy orbit starting at swapFidelity(w). Refinement gives PSD, trace p and
conditional PSD with unit trace. The general tree is homogeneous of degree 2^m;
the composed schedule is homogeneous of degree equal to its raw resource count,
the product of 2^(m+1). Spatial segment count is 2^length.

Empty schedules preserve the input. All-zero schedules have weight one and pure
swapping visibility w0^(2^k). Constant depth with unit quality reduces to the ideal
nestedRepeaterMatrix. LocalQualityGain requires nondecrease at each actual step;
under this hypothesis every prefix retains initial quality. This does not assert
that an arbitrary schedule satisfies the hypothesis.

Regressions distinguish chronological order, noise-dependent weights and the
ideal resource-saving schedule 4 then 2 from its reversal. The ideal witness is
not a noisy witness or an optimality claim. No resource yield, retries, variable
noise, noisy swapping, adaptive controller or linearity of the diagonal resource
preparation is claimed. All physical claims use Visibility inputs.

## Theorems

- [`QuantumScheduledNoisyRepeater.noisyGeneralTree_werner`](../../Verification/QuantumScheduledNoisyRepeater.lean#L26)
- [`QuantumScheduledNoisyRepeater.noisyGeneralTree_smul`](../../Verification/QuantumScheduledNoisyRepeater.lean#L32)
- [`QuantumScheduledNoisyRepeater.noisyOrbit_quarter_bounds`](../../Verification/QuantumScheduledNoisyRepeater.lean#L45)
- [`QuantumScheduledNoisyRepeater.noisyLevelVisibility_bounds`](../../Verification/QuantumScheduledNoisyRepeater.lean#L61)
- [`QuantumScheduledNoisyRepeater.noisyLevelProbability_bounds`](../../Verification/QuantumScheduledNoisyRepeater.lean#L78)
- [`QuantumScheduledNoisyRepeater.noisyRepeaterLevelStep_smul`](../../Verification/QuantumScheduledNoisyRepeater.lean#L87)
- [`QuantumScheduledNoisyRepeater.noisyRepeaterLevelStep_isotropic`](../../Verification/QuantumScheduledNoisyRepeater.lean#L94)
- [`QuantumScheduledNoisyRepeater.scheduledStepAcc_valid`](../../Verification/QuantumScheduledNoisyRepeater.lean#L144)
- [`QuantumScheduledNoisyRepeater.scheduledFold_valid`](../../Verification/QuantumScheduledNoisyRepeater.lean#L153)
- [`QuantumScheduledNoisyRepeater.scheduledState_valid`](../../Verification/QuantumScheduledNoisyRepeater.lean#L159)
- [`QuantumScheduledNoisyRepeater.scheduledState_append`](../../Verification/QuantumScheduledNoisyRepeater.lean#L163)
- [`QuantumScheduledNoisyRepeater.scheduledState_snoc`](../../Verification/QuantumScheduledNoisyRepeater.lean#L167)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_snoc`](../../Verification/QuantumScheduledNoisyRepeater.lean#L171)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterProbability_snoc`](../../Verification/QuantumScheduledNoisyRepeater.lean#L176)
- [`QuantumScheduledNoisyRepeater.scheduledVisibilityValue_snoc`](../../Verification/QuantumScheduledNoisyRepeater.lean#L182)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_refinement`](../../Verification/QuantumScheduledNoisyRepeater.lean#L188)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterProbability_pos`](../../Verification/QuantumScheduledNoisyRepeater.lean#L192)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterProbability_le_one`](../../Verification/QuantumScheduledNoisyRepeater.lean#L195)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_posSemidef`](../../Verification/QuantumScheduledNoisyRepeater.lean#L198)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_trace`](../../Verification/QuantumScheduledNoisyRepeater.lean#L203)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_conditional`](../../Verification/QuantumScheduledNoisyRepeater.lean#L207)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_conditional_density`](../../Verification/QuantumScheduledNoisyRepeater.lean#L214)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_nil`](../../Verification/QuantumScheduledNoisyRepeater.lean#L221)
- [`QuantumScheduledNoisyRepeater.scheduledRawPairCount_append`](../../Verification/QuantumScheduledNoisyRepeater.lean#L228)
- [`QuantumScheduledNoisyRepeater.scheduledSegmentCount_append`](../../Verification/QuantumScheduledNoisyRepeater.lean#L232)
- [`QuantumScheduledNoisyRepeater.noisyRepeaterLevelStep_zero`](../../Verification/QuantumScheduledNoisyRepeater.lean#L236)
- [`QuantumScheduledNoisyRepeater.noisyLevelVisibilityValue_zero`](../../Verification/QuantumScheduledNoisyRepeater.lean#L239)
- [`QuantumScheduledNoisyRepeater.scheduled_zero_depths`](../../Verification/QuantumScheduledNoisyRepeater.lean#L244)
- [`QuantumScheduledNoisyRepeater.noisyGeneralTree_unit`](../../Verification/QuantumScheduledNoisyRepeater.lean#L262)
- [`QuantumScheduledNoisyRepeater.scheduledRepeaterMatrix_ideal_replicate`](../../Verification/QuantumScheduledNoisyRepeater.lean#L271)
- [`QuantumScheduledNoisyRepeater.scheduledFold_matrix_smul`](../../Verification/QuantumScheduledNoisyRepeater.lean#L281)
- [`QuantumScheduledNoisyRepeater.scheduledRawPairCount_replicate`](../../Verification/QuantumScheduledNoisyRepeater.lean#L297)
- [`QuantumScheduledNoisyRepeater.scheduledVisibilityValue_bounds`](../../Verification/QuantumScheduledNoisyRepeater.lean#L305)
- [`QuantumScheduledNoisyRepeater.scheduledVisibility_prefix_sustains_initial_of_local_gain`](../../Verification/QuantumScheduledNoisyRepeater.lean#L315)
- [`QuantumScheduledNoisyRepeater.scheduledVisibility_sustains_initial_of_local_gain`](../../Verification/QuantumScheduledNoisyRepeater.lean#L328)
- [`QuantumScheduledNoisyRepeater.verification_suite`](../../Verification/QuantumScheduledNoisyRepeater.lean#L340)

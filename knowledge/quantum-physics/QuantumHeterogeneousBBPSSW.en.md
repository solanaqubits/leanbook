---
id: QuantumHeterogeneousBBPSSW
language: en
section: quantum-physics
source: Verification/QuantumHeterogeneousBBPSSW.lean
source_sha256: 0865b49e467fbd308124162670bf3da676c1434b601417af68070b5cabfe4367
novelty: not-assessed
status: reviewed
---

# QuantumHeterogeneousBBPSSW

[Section](README.md) · [Scope](../../docs/quantum-v4.31.md) ·
[Source](../../Verification/QuantumHeterogeneousBBPSSW.lean)

The existing bilateral circuit is evaluated on two unequal, independently prepared
Werner resources. A polynomial twirled matrix identity holds for all real inputs;
the representation P2 W(R2) requires P2 nonzero. On the physical square [0,1]^2,
1/3 <= P2 <= 1 and 0 <= R2 <= 1, with PSD trace-one conditional output.
The exact threshold for improving either resource depends on both fidelities.
Symmetry, the diagonal specialization and simultaneous improvement are proved.
A nonphysical zero-trace nonzero output witnesses the need for the nonzero premise.

The actual perfect-readout wernerRound from v4.27 supplies two independent
swapped pairs to purified. Matrix refinement connects this operator to the scalar
law R((1+3w^2)/4). One step never restores the initial segment fidelity for
0<w<1; it improves the swapped fidelity when w^2>1/3. The v4.30 limit theorem
proves that every sufficiently large depth exceeds the segment fidelity.

No noisy-gate threshold, optimal resource allocation, recycling yield or general
correlated-resource formula is claimed. Two independent swapped inputs consume
four elementary pairs; a depth-n purification tree consumes 2^n swapped pairs.

## Theorems

- [`QuantumHeterogeneousBBPSSW.heteroSuccessProb_symm`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L30)
- [`QuantumHeterogeneousBBPSSW.heteroRecurrence_symm`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L33)
- [`QuantumHeterogeneousBBPSSW.heteroSuccessProb_diag`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L39)
- [`QuantumHeterogeneousBBPSSW.heteroRecurrence_diag`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L42)
- [`QuantumHeterogeneousBBPSSW.accepted_hetero_row00`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L54)
- [`QuantumHeterogeneousBBPSSW.accepted_hetero_row01`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L65)
- [`QuantumHeterogeneousBBPSSW.accepted_hetero_row10`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L78)
- [`QuantumHeterogeneousBBPSSW.accepted_hetero_row11`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L91)
- [`QuantumHeterogeneousBBPSSW.accepted_hetero_matrix`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L103)
- [`QuantumHeterogeneousBBPSSW.accepted_hetero_trace`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L113)
- [`QuantumHeterogeneousBBPSSW.accepted_hetero_target`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L120)
- [`QuantumHeterogeneousBBPSSW.purified_hetero_isotropic`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L125)
- [`QuantumHeterogeneousBBPSSW.purified_hetero_werner`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L133)
- [`QuantumHeterogeneousBBPSSW.heteroSuccessProb_bounds`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L146)
- [`QuantumHeterogeneousBBPSSW.heteroSuccessProb_pos`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L155)
- [`QuantumHeterogeneousBBPSSW.heteroRecurrence_bounds`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L158)
- [`QuantumHeterogeneousBBPSSW.purified_hetero_conditional`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L171)
- [`QuantumHeterogeneousBBPSSW.purified_hetero_conditional_density`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L177)
- [`QuantumHeterogeneousBBPSSW.heteroRecurrence_sub_left`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L185)
- [`QuantumHeterogeneousBBPSSW.threshold_denom_pos`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L193)
- [`QuantumHeterogeneousBBPSSW.hetero_strict_improve_left_iff`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L197)
- [`QuantumHeterogeneousBBPSSW.hetero_strict_improve_max_iff`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L208)
- [`QuantumHeterogeneousBBPSSW.threshold_sub_self`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L215)
- [`QuantumHeterogeneousBBPSSW.hetero_counterexample_three_quarters_three_fifths`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L222)
- [`QuantumHeterogeneousBBPSSW.nonphysical_zero_weight_nonzero_output`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L227)
- [`QuantumHeterogeneousBBPSSW.swap_success_probability`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L241)
- [`QuantumHeterogeneousBBPSSW.swap_then_purify_sub_elem`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L245)
- [`QuantumHeterogeneousBBPSSW.swap_then_purify_lt_elem`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L255)
- [`QuantumHeterogeneousBBPSSW.swap_then_one_purify_sandwich`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L266)
- [`QuantumHeterogeneousBBPSSW.eventually_purification_exceeds_elem`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L275)
- [`QuantumHeterogeneousBBPSSW.exists_purification_depth_exceeding_elemFidelity`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L283)
- [`QuantumHeterogeneousBBPSSW.isotropic_eq_werner`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L289)
- [`QuantumHeterogeneousBBPSSW.swapOutput_matrix`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L301)
- [`QuantumHeterogeneousBBPSSW.swapThenPurify_matrix`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L314)
- [`QuantumHeterogeneousBBPSSW.swapThenPurify_conditional`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L321)
- [`QuantumHeterogeneousBBPSSW.verification_suite`](../../Verification/QuantumHeterogeneousBBPSSW.lean#L338)

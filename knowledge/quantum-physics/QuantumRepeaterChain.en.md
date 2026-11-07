---
id: QuantumRepeaterChain
language: en
section: quantum-physics
source: Verification/QuantumRepeaterChain.lean
source_sha256: 1b746e132d4fd26259815ac6de221a09726afa37c6048a0afe90c6e560fdf135
novelty: not-assessed
status: reviewed
---

# QuantumRepeaterChain

[Section](README.md) · [Scope](../../docs/quantum-v4.32.md) ·
[Source](../../Verification/QuantumRepeaterChain.lean)

Finite homogeneous ideal repeater with one perfect BSM swapping operation and
one BBPSSW purification round per level. A node consumes four independent child
resources: two swaps produce the two inputs to purified. The unnormalized
recursive matrix is defined by these existing operators, without early conditioning.

For every finite depth k, the matrix is p_k times the isotropic matrix with bounded
visibility w_k. Its trace is p_k>0, p_k<=1, and its conditional matrix is PSD with
trace one. Visibility follows T(w)=2w^2(1+2w^2)/(3(1+w^4)); all-success weight follows
p_(k+1)=p_k^4(1+w_k^4)/2, with an exact product using exponents 4^(k-1-j).
Spatial span doubles per level, while resources quadruple: 2^k segments, 4^k raw
pairs, equivalently 2^k raw copies per segment in this homogeneous construction.

One purification round per level does not preserve segment fidelity: visibility
is nonincreasing, and strictly decreases for initial 0<w<1. No positive long-distance
quality bound, orbit limit, scheduling, memory decoherence, detector losses,
expected yield, cloning map or general correlated-input theorem is claimed.
The repeated-copy parametrization is nonlinear; inherited CP maps act on their
full joint inputs before normalization. The result constructs a postselected
end-to-end pair, not a deterministic channel with a specified transmission rate.

## Theorems

- [`QuantumRepeaterChain.nodeProbability_bounds`](../../Verification/QuantumRepeaterChain.lean#L24)
- [`QuantumRepeaterChain.nodeProbability_pos`](../../Verification/QuantumRepeaterChain.lean#L30)
- [`QuantumRepeaterChain.nodeVisibility_bounds`](../../Verification/QuantumRepeaterChain.lean#L34)
- [`QuantumRepeaterChain.node_fidelity`](../../Verification/QuantumRepeaterChain.lean#L45)
- [`QuantumRepeaterChain.node_visibility_strict_decay`](../../Verification/QuantumRepeaterChain.lean#L54)
- [`QuantumRepeaterChain.node_visibility_nonincrease`](../../Verification/QuantumRepeaterChain.lean#L61)
- [`QuantumRepeaterChain.visibilityAt_recurrence`](../../Verification/QuantumRepeaterChain.lean#L77)
- [`QuantumRepeaterChain.visibilityAt_antitone`](../../Verification/QuantumRepeaterChain.lean#L82)
- [`QuantumRepeaterChain.visibilityAt_interior`](../../Verification/QuantumRepeaterChain.lean#L87)
- [`QuantumRepeaterChain.visibilityAt_strictAnti`](../../Verification/QuantumRepeaterChain.lean#L99)
- [`QuantumRepeaterChain.fidelityAt_recurrence`](../../Verification/QuantumRepeaterChain.lean#L106)
- [`QuantumRepeaterChain.fidelityAt_nonincrease`](../../Verification/QuantumRepeaterChain.lean#L110)
- [`QuantumRepeaterChain.pairSwap_isotropic`](../../Verification/QuantumRepeaterChain.lean#L120)
- [`QuantumRepeaterChain.pairSwap_common_smul`](../../Verification/QuantumRepeaterChain.lean#L126)
- [`QuantumRepeaterChain.repeaterNode_isotropic`](../../Verification/QuantumRepeaterChain.lean#L135)
- [`QuantumRepeaterChain.repeaterNode_common_smul`](../../Verification/QuantumRepeaterChain.lean#L147)
- [`QuantumRepeaterChain.repeaterProbability_pos`](../../Verification/QuantumRepeaterChain.lean#L166)
- [`QuantumRepeaterChain.repeaterProbability_le_one`](../../Verification/QuantumRepeaterChain.lean#L171)
- [`QuantumRepeaterChain.repeaterProbability_closed_form`](../../Verification/QuantumRepeaterChain.lean#L179)
- [`QuantumRepeaterChain.repeaterMatrix_refinement`](../../Verification/QuantumRepeaterChain.lean#L196)
- [`QuantumRepeaterChain.repeaterMatrix_positive`](../../Verification/QuantumRepeaterChain.lean#L204)
- [`QuantumRepeaterChain.repeaterMatrix_trace`](../../Verification/QuantumRepeaterChain.lean#L208)
- [`QuantumRepeaterChain.repeaterMatrix_conditional`](../../Verification/QuantumRepeaterChain.lean#L212)
- [`QuantumRepeaterChain.repeaterMatrix_conditional_density`](../../Verification/QuantumRepeaterChain.lean#L217)
- [`QuantumRepeaterChain.repeaterMatrix_conditional_fidelity`](../../Verification/QuantumRepeaterChain.lean#L224)
- [`QuantumRepeaterChain.segmentCount_eq`](../../Verification/QuantumRepeaterChain.lean#L235)
- [`QuantumRepeaterChain.rawPairCount_eq`](../../Verification/QuantumRepeaterChain.lean#L240)
- [`QuantumRepeaterChain.rawPairCount_per_segment`](../../Verification/QuantumRepeaterChain.lean#L245)
- [`QuantumRepeaterChain.verification_suite`](../../Verification/QuantumRepeaterChain.lean#L258)

---
id: QuantumBBPSSWConvergence
language: en
section: quantum-physics
source: Verification/QuantumBBPSSWConvergence.lean
source_sha256: 3d40f68bbcabdab5f82556c9452362ace6495a4d5ec9b246221cf97c1ea4e275
novelty: not-assessed
status: reviewed
---

# QuantumBBPSSWConvergence

[Section](README.md) · [Scope](../../docs/quantum-v4.30.md) ·
[Source](../../Verification/QuantumBBPSSWConvergence.lean)

Exact barriers and invariant fidelity intervals for ideal BBPSSW. The three
nonstationary orbit regions have strict monotonicity. Order completeness,
continuity and the fixed-point classification prove Tendsto to 1 above 1/2
(including the stationary endpoint 1), and to 1/4 below 1/2 (including 0 and 1/4).
The threshold 1/2 remains stationary, not part of either attraction theorem.

The recursively constructed unnormalized operator tree consumes two independent
subtrees at every node. Its matrix equals p_n W(F_n), with p_(n+1)=p_n^2 P(F_n)
and the exact product exponents 2^(n-1-k). Positivity of p_n holds algebraically
for all real inputs; the probability bound p_n <= 1 and PSD require F in [0,1].
Trace, conditional normalization and trace-one conditional PSD are proved.
No convergence rate, noisy threshold, expected resource yield, recycling policy
or correlated-resource recurrence is claimed. The tree probability requires
all internal nodes to succeed; it is not the simple product of level probabilities.

## Theorems

- [`QuantumBBPSSWConvergence.recurrence_sub_quarter`](../../Verification/QuantumBBPSSWConvergence.lean#L18)
- [`QuantumBBPSSWConvergence.one_sub_recurrence`](../../Verification/QuantumBBPSSWConvergence.lean#L25)
- [`QuantumBBPSSWConvergence.recurrence_lt_one`](../../Verification/QuantumBBPSSWConvergence.lean#L32)
- [`QuantumBBPSSWConvergence.recurrence_invariant_above_half`](../../Verification/QuantumBBPSSWConvergence.lean#L39)
- [`QuantumBBPSSWConvergence.recurrence_invariant_quarter_to_half`](../../Verification/QuantumBBPSSWConvergence.lean#L44)
- [`QuantumBBPSSWConvergence.recurrence_invariant_below_quarter`](../../Verification/QuantumBBPSSWConvergence.lean#L52)
- [`QuantumBBPSSWConvergence.fidelityOrbit_zero`](../../Verification/QuantumBBPSSWConvergence.lean#L62)
- [`QuantumBBPSSWConvergence.fidelityOrbit_succ`](../../Verification/QuantumBBPSSWConvergence.lean#L64)
- [`QuantumBBPSSWConvergence.fidelityOrbit_fixed`](../../Verification/QuantumBBPSSWConvergence.lean#L68)
- [`QuantumBBPSSWConvergence.fidelityOrbit_bounds`](../../Verification/QuantumBBPSSWConvergence.lean#L74)
- [`QuantumBBPSSWConvergence.fidelityOrbit_above_half`](../../Verification/QuantumBBPSSWConvergence.lean#L80)
- [`QuantumBBPSSWConvergence.fidelityOrbit_quarter_to_half`](../../Verification/QuantumBBPSSWConvergence.lean#L86)
- [`QuantumBBPSSWConvergence.fidelityOrbit_below_quarter`](../../Verification/QuantumBBPSSWConvergence.lean#L94)
- [`QuantumBBPSSWConvergence.fidelityOrbit_strictMono_above_half`](../../Verification/QuantumBBPSSWConvergence.lean#L103)
- [`QuantumBBPSSWConvergence.fidelityOrbit_strictAnti_quarter_to_half`](../../Verification/QuantumBBPSSWConvergence.lean#L110)
- [`QuantumBBPSSWConvergence.fidelityOrbit_strictMono_below_quarter`](../../Verification/QuantumBBPSSWConvergence.lean#L117)
- [`QuantumBBPSSWConvergence.continuous_recurrence`](../../Verification/QuantumBBPSSWConvergence.lean#L124)
- [`QuantumBBPSSWConvergence.orbit_limit_fixed`](../../Verification/QuantumBBPSSWConvergence.lean#L130)
- [`QuantumBBPSSWConvergence.fidelityOrbit_tendsto_one`](../../Verification/QuantumBBPSSWConvergence.lean#L138)
- [`QuantumBBPSSWConvergence.fidelityOrbit_tendsto_quarter`](../../Verification/QuantumBBPSSWConvergence.lean#L156)
- [`QuantumBBPSSWConvergence.treeProbability_pos`](../../Verification/QuantumBBPSSWConvergence.lean#L193)
- [`QuantumBBPSSWConvergence.treeProbability_closed_form`](../../Verification/QuantumBBPSSWConvergence.lean#L198)
- [`QuantumBBPSSWConvergence.treeProbability_two`](../../Verification/QuantumBBPSSWConvergence.lean#L216)
- [`QuantumBBPSSWConvergence.treeMatrix_eq_werner`](../../Verification/QuantumBBPSSWConvergence.lean#L220)
- [`QuantumBBPSSWConvergence.treeMatrix_conditional`](../../Verification/QuantumBBPSSWConvergence.lean#L230)
- [`QuantumBBPSSWConvergence.successProbability_le_one`](../../Verification/QuantumBBPSSWConvergence.lean#L235)
- [`QuantumBBPSSWConvergence.treeProbability_le_one`](../../Verification/QuantumBBPSSWConvergence.lean#L240)
- [`QuantumBBPSSWConvergence.werner_trace`](../../Verification/QuantumBBPSSWConvergence.lean#L250)
- [`QuantumBBPSSWConvergence.treeMatrix_trace`](../../Verification/QuantumBBPSSWConvergence.lean#L255)
- [`QuantumBBPSSWConvergence.treeMatrix_positive`](../../Verification/QuantumBBPSSWConvergence.lean#L259)
- [`QuantumBBPSSWConvergence.treeMatrix_conditional_positive`](../../Verification/QuantumBBPSSWConvergence.lean#L264)
- [`QuantumBBPSSWConvergence.treeMatrix_conditional_trace`](../../Verification/QuantumBBPSSWConvergence.lean#L269)
- [`QuantumBBPSSWConvergence.verification_suite`](../../Verification/QuantumBBPSSWConvergence.lean#L279)

---
id: QuantumBBPSSWDistillation
language: en
section: quantum-physics
source: Verification/QuantumBBPSSWDistillation.lean
source_sha256: 4a4550887bfef49034bc11df86673b6520e6952cc01e8165d822bbffea104228
novelty: not-assessed
status: reviewed
---

# QuantumBBPSSWDistillation

[Section](README.md) · [Scope](../../docs/quantum-v4.29.md) ·
[Source](../../Verification/QuantumBBPSSWDistillation.lean)

Ideal bilateral CNOT in pair-major order, rectangular target measurements,
CP accept/reject branches and full trace balance. For two independent Werner
resources with fidelity F in [0,1], the accepted Bell weights are derived
entrywise. The finite local twirl yields P(F) times W(R(F)). Conditional PSD,
trace one, positive denominator, exact fixed points and the three strict sign
regions are proved. No cloning channel, gate-noise threshold, repeated-round
convergence, resource yield or general correlated-input recurrence is claimed.

## Theorems

- [`QuantumBBPSSWDistillation.flip_involutive`](../../Verification/QuantumBBPSSWDistillation.lean#L23)
- [`QuantumBBPSSWDistillation.flip_eq`](../../Verification/QuantumBBPSSWDistillation.lean#L27)
- [`QuantumBBPSSWDistillation.biCNOT_left`](../../Verification/QuantumBBPSSWDistillation.lean#L34)
- [`QuantumBBPSSWDistillation.biCNOT_right`](../../Verification/QuantumBBPSSWDistillation.lean#L37)
- [`QuantumBBPSSWDistillation.biCNOT_adjoint`](../../Verification/QuantumBBPSSWDistillation.lean#L40)
- [`QuantumBBPSSWDistillation.biCNOT_unitary`](../../Verification/QuantumBBPSSWDistillation.lean#L46)
- [`QuantumBBPSSWDistillation.branch_entry`](../../Verification/QuantumBBPSSWDistillation.lean#L57)
- [`QuantumBBPSSWDistillation.accepted_entry`](../../Verification/QuantumBBPSSWDistillation.lean#L72)
- [`QuantumBBPSSWDistillation.instrument_cp`](../../Verification/QuantumBBPSSWDistillation.lean#L82)
- [`QuantumBBPSSWDistillation.instrument_trace`](../../Verification/QuantumBBPSSWDistillation.lean#L85)
- [`QuantumBBPSSWDistillation.werner_distribution`](../../Verification/QuantumBBPSSWDistillation.lean#L113)
- [`QuantumBBPSSWDistillation.werner_positive`](../../Verification/QuantumBBPSSWDistillation.lean#L118)
- [`QuantumBBPSSWDistillation.probability_positive`](../../Verification/QuantumBBPSSWDistillation.lean#L126)
- [`QuantumBBPSSWDistillation.recurrence_difference`](../../Verification/QuantumBBPSSWDistillation.lean#L130)
- [`QuantumBBPSSWDistillation.improves_above_threshold`](../../Verification/QuantumBBPSSWDistillation.lean#L137)
- [`QuantumBBPSSWDistillation.improves_below_quarter`](../../Verification/QuantumBBPSSWDistillation.lean#L144)
- [`QuantumBBPSSWDistillation.decreases_between_fixed_points`](../../Verification/QuantumBBPSSWDistillation.lean#L152)
- [`QuantumBBPSSWDistillation.accepted_werner_matrix`](../../Verification/QuantumBBPSSWDistillation.lean#L164)
- [`QuantumBBPSSWDistillation.accepted_probability`](../../Verification/QuantumBBPSSWDistillation.lean#L178)
- [`QuantumBBPSSWDistillation.accepted_target_mass`](../../Verification/QuantumBBPSSWDistillation.lean#L185)
- [`QuantumBBPSSWDistillation.normalized_fidelity`](../../Verification/QuantumBBPSSWDistillation.lean#L190)
- [`QuantumBBPSSWDistillation.fixed_points`](../../Verification/QuantumBBPSSWDistillation.lean#L198)
- [`QuantumBBPSSWDistillation.purified_cp`](../../Verification/QuantumBBPSSWDistillation.lean#L218)
- [`QuantumBBPSSWDistillation.purified_add`](../../Verification/QuantumBBPSSWDistillation.lean#L220)
- [`QuantumBBPSSWDistillation.purified_smul`](../../Verification/QuantumBBPSSWDistillation.lean#L226)
- [`QuantumBBPSSWDistillation.purified_trace_balance`](../../Verification/QuantumBBPSSWDistillation.lean#L231)
- [`QuantumBBPSSWDistillation.recurrence_bounds`](../../Verification/QuantumBBPSSWDistillation.lean#L235)
- [`QuantumBBPSSWDistillation.purified_werner`](../../Verification/QuantumBBPSSWDistillation.lean#L245)
- [`QuantumBBPSSWDistillation.purified_conditional`](../../Verification/QuantumBBPSSWDistillation.lean#L259)
- [`QuantumBBPSSWDistillation.purified_conditional_positive`](../../Verification/QuantumBBPSSWDistillation.lean#L265)
- [`QuantumBBPSSWDistillation.purified_conditional_trace`](../../Verification/QuantumBBPSSWDistillation.lean#L270)
- [`QuantumBBPSSWDistillation.verification_suite`](../../Verification/QuantumBBPSSWDistillation.lean#L282)

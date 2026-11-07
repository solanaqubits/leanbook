---
id: QuantumNoisyBBPSSW
language: en
section: quantum-physics
source: Verification/QuantumNoisyBBPSSW.lean
source_sha256: 5b5821b8f3f3d59fcd889ab81b77e86e18e3567172b3cb05db6ba98cf402f2eb
novelty: not-assessed
status: reviewed
---

# QuantumNoisyBBPSSW

[Section](README.md) · [Scope](../../docs/quantum-v4.34.md) ·
[Source](../../Verification/QuantumNoisyBBPSSW.lean)

Post-depolarization acts on the entire retained two-qubit pair after ideal BBPSSW,
using the existing CPTP channel depolarizing with a bounded Visibility parameter.
The composite unnormalized map is CP, complex linear, positive, and has the same
trace as purified on every input matrix. Together with the unchanged reject
branch it preserves total trace. On two independent Werner inputs it yields
P(F) times W(R_gamma(F)), where R_gamma(F)=(1-gamma)/4+gamma*R(F).
This matrix identity holds for all real F; conditional density properties are
proved on the full physical range F in [0,1], including F below 1/4.

The increment has cubic numerator (4F-1)*Delta_gamma(F), with the quadratic
factor Delta=-8F²+4(2*gamma+1)*F-(5-gamma). A completed-square identity gives
three discriminant regimes. For 0<=gamma<criticalGamma, 1/4 is the only real
fixed point and every F>1/4 strictly decreases. At criticalGamma the quadratic
has a double root (2*criticalGamma+1)/4; there is no strict gain above 1/4.
For criticalGamma<gamma<1, the two roots lie strictly between 1/2 and one,
and F>1/4 improves exactly between those roots. All fixed points are classified.

criticalGamma=3*(sqrt(5)-1)/4. The upper root is a stationary ceiling, strictly
below the one-step output R_gamma(1), which is itself below one. At gamma=19/20,
R_gamma(3/4)=99/130, R_gamma(1)=77/80, and the upper root is
(29+sqrt(31))/40. Gamma=9/10 has no working window. Gamma=1 and gamma=0 recover
the ideal recurrence and constant fidelity 1/4 respectively.

This is not a model of noise inside bilateral CNOT, input depolarization, detector
errors, or a complete noisy repeater. No iteration limit, yield or rate theorem
is asserted. CP and linearity concern unnormalized joint inputs; preparing two
independent copies and conditional normalization are separate operations.

## Theorems

- [`QuantumNoisyBBPSSW.noisyRecurrence_sub_self`](../../Verification/QuantumNoisyBBPSSW.lean#L34)
- [`QuantumNoisyBBPSSW.noisyRecurrence_bounds`](../../Verification/QuantumNoisyBBPSSW.lean#L42)
- [`QuantumNoisyBBPSSW.noisyRecurrence_quarter`](../../Verification/QuantumNoisyBBPSSW.lean#L52)
- [`QuantumNoisyBBPSSW.noisyRecurrence_one`](../../Verification/QuantumNoisyBBPSSW.lean#L56)
- [`QuantumNoisyBBPSSW.noisyRecurrence_zero`](../../Verification/QuantumNoisyBBPSSW.lean#L59)
- [`QuantumNoisyBBPSSW.noisyRecurrence_pure_input`](../../Verification/QuantumNoisyBBPSSW.lean#L62)
- [`QuantumNoisyBBPSSW.criticalGamma_bounds`](../../Verification/QuantumNoisyBBPSSW.lean#L66)
- [`QuantumNoisyBBPSSW.noisyDiscFactor_critical`](../../Verification/QuantumNoisyBBPSSW.lean#L72)
- [`QuantumNoisyBBPSSW.noisyDiscFactor_sub`](../../Verification/QuantumNoisyBBPSSW.lean#L77)
- [`QuantumNoisyBBPSSW.noisyDiscFactor_neg`](../../Verification/QuantumNoisyBBPSSW.lean#L82)
- [`QuantumNoisyBBPSSW.noisyDiscFactor_pos`](../../Verification/QuantumNoisyBBPSSW.lean#L90)
- [`QuantumNoisyBBPSSW.noisyIncrementQuad_square`](../../Verification/QuantumNoisyBBPSSW.lean#L99)
- [`QuantumNoisyBBPSSW.noisyRecurrence_fixed_iff_quad`](../../Verification/QuantumNoisyBBPSSW.lean#L104)
- [`QuantumNoisyBBPSSW.noisyRecurrence_strict_decay_below_critical`](../../Verification/QuantumNoisyBBPSSW.lean#L118)
- [`QuantumNoisyBBPSSW.noisyRecurrence_subcritical_fixed_iff`](../../Verification/QuantumNoisyBBPSSW.lean#L130)
- [`QuantumNoisyBBPSSW.noisyIncrementQuad_critical`](../../Verification/QuantumNoisyBBPSSW.lean#L139)
- [`QuantumNoisyBBPSSW.noisyRecurrence_critical_no_strict_gain`](../../Verification/QuantumNoisyBBPSSW.lean#L144)
- [`QuantumNoisyBBPSSW.noisyRecurrence_critical_fixed_iff`](../../Verification/QuantumNoisyBBPSSW.lean#L154)
- [`QuantumNoisyBBPSSW.noisyIncrementQuad_roots`](../../Verification/QuantumNoisyBBPSSW.lean#L166)
- [`QuantumNoisyBBPSSW.working_window_inside_half_one`](../../Verification/QuantumNoisyBBPSSW.lean#L173)
- [`QuantumNoisyBBPSSW.noisyRecurrence_strict_improve_iff_in_window`](../../Verification/QuantumNoisyBBPSSW.lean#L190)
- [`QuantumNoisyBBPSSW.noisyRecurrence_fixed_points_iff`](../../Verification/QuantumNoisyBBPSSW.lean#L222)
- [`QuantumNoisyBBPSSW.critical_window_bounds_coincide`](../../Verification/QuantumNoisyBBPSSW.lean#L229)
- [`QuantumNoisyBBPSSW.noisyRecurrence_strictMonoOn`](../../Verification/QuantumNoisyBBPSSW.lean#L234)
- [`QuantumNoisyBBPSSW.ceiling_lt_pure_output`](../../Verification/QuantumNoisyBBPSSW.lean#L242)
- [`QuantumNoisyBBPSSW.noisyPurified_isCPMap`](../../Verification/QuantumNoisyBBPSSW.lean#L254)
- [`QuantumNoisyBBPSSW.noisyPurified_add`](../../Verification/QuantumNoisyBBPSSW.lean#L263)
- [`QuantumNoisyBBPSSW.noisyPurified_smul`](../../Verification/QuantumNoisyBBPSSW.lean#L267)
- [`QuantumNoisyBBPSSW.noisyPurified_trace`](../../Verification/QuantumNoisyBBPSSW.lean#L271)
- [`QuantumNoisyBBPSSW.noisyPurified_trace_balance`](../../Verification/QuantumNoisyBBPSSW.lean#L274)
- [`QuantumNoisyBBPSSW.noisyPurified_posSemidef`](../../Verification/QuantumNoisyBBPSSW.lean#L278)
- [`QuantumNoisyBBPSSW.depolarizing_werner`](../../Verification/QuantumNoisyBBPSSW.lean#L287)
- [`QuantumNoisyBBPSSW.noisyPurified_werner`](../../Verification/QuantumNoisyBBPSSW.lean#L293)
- [`QuantumNoisyBBPSSW.noisyPurified_success_probability`](../../Verification/QuantumNoisyBBPSSW.lean#L299)
- [`QuantumNoisyBBPSSW.noisyPurified_conditional`](../../Verification/QuantumNoisyBBPSSW.lean#L303)
- [`QuantumNoisyBBPSSW.noisyPurified_conditional_density`](../../Verification/QuantumNoisyBBPSSW.lean#L309)
- [`QuantumNoisyBBPSSW.nine_tenths_below_critical`](../../Verification/QuantumNoisyBBPSSW.lean#L318)
- [`QuantumNoisyBBPSSW.nine_tenths_no_working_window`](../../Verification/QuantumNoisyBBPSSW.lean#L324)
- [`QuantumNoisyBBPSSW.nineteen_twentieths_above_critical`](../../Verification/QuantumNoisyBBPSSW.lean#L328)
- [`QuantumNoisyBBPSSW.nineteen_twentieths_ceiling`](../../Verification/QuantumNoisyBBPSSW.lean#L334)
- [`QuantumNoisyBBPSSW.nineteen_twentieths_working_window_witness`](../../Verification/QuantumNoisyBBPSSW.lean#L341)
- [`QuantumNoisyBBPSSW.verification_suite`](../../Verification/QuantumNoisyBBPSSW.lean#L363)

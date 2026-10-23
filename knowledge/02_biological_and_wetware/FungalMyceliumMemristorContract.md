---
id: FungalMyceliumMemristorContract
language: en
section: quantum-physics
source: Verification/FungalMyceliumMemristorContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 3db5a6cf089f0b71d646c9f391a32d79ce85b5ecfd54d2d9a7422697769555a6
---

# Bounded conductance, order memory and spatial attenuation

[Section](../quantum-physics/README.md) · [Lean](../../Verification/FungalMyceliumMemristorContract.lean)

Stage ε271 formalizes three prescribed components separately: conductance state,
a spike threshold, and spatial amplitude. Their shared suite does not establish
a causal or energetic connection within living mycelium.

## State and active thresholds

`MemristorParameters` stores rational `Gmin`, `Gmax`, `Vth`, `alphaUp`,
`alphaDown`, with proofs of `0 < Gmin < Gmax`, `0 < Vth`,
`0 < alphaUp ≤ 1`, `0 < alphaDown ≤ 1`. `MemristorState p`
(alias `MyceliumNodeState p`) stores `conductance : ℚ` in [Gmin,Gmax].

`upStep` is U(G)=G+alphaUp·(Gmax−G);
`downStep` is D(G)=G−alphaDown·(G−Gmin).
These are convex affine steps toward the corresponding endpoints.
`memristorStep s V` selects U for V≥Vth, D for V≤−Vth, and the identity
otherwise. Positive Vth prevents overlap of the active branches. Both ±Vth
endpoints are active; retention is guaranteed in the strict band |V|<Vth.
V=0 preserves state. Relaxation to a separate Gbase was not selected.

The proofs establish bounds, a nondecreasing positive active step, and a
nonincreasing negative active step. Increase is strict for G<Gmax; decrease
is strict for Gmin<G. At the corresponding endpoint the step is the identity;
a coefficient of 1 permits reaching the endpoint in one step. Coefficients
refer to an abstract event: duration and rate dependence on voltage beyond
the threshold are unspecified. Conductance and voltage names carry no physical
unit calibration.

## Order memory and conditional current

Monotonicity alone is insufficient to establish memory. A separate proof gives
`U(D(G))−D(U(G)) = alphaUp·alphaDown·(Gmax−Gmin) > 0`.
The order of the same two admissible opposite drives therefore changes the
final state. `threshold_history_dependence` expresses this through complete
steps at +Vth and −Vth. With Gmin=1,Gmax=3,G=2 and both coefficients 1/2,
D(U(G))=7/4 and U(D(G))=9/4. This is algebraic memory of the chosen rule,
not a measured hysteresis loop.

`current s V = G·V` is linear in V by definition at fixed state.
`common_probe_history` uses the same probe V with 0<V<Vth: both historical
states are retained, and current after D(U(G)) is strictly below current
after U(D(G)). This distinguishes histories under a common model input;
no physical measurement protocol is specified.
`power s V = G·V²`; the proofs give `power = current·V` and nonnegativity.
This concerns the prescribed branch: conductance-update energy, external
supply, storage and the whole network are not modeled. It does not prove a
complete energy balance or passivity of a biological device. History-dependent
G is not empirical validation of a nonlinear I–V curve.

## Strict one-sided spike rule

`spikeGenerator Sth S : Bool` is `decide (Sth < S)` for arbitrary rational
Sth and S. Equality to the threshold is always inactive. Interpreting a spike
as requiring a positive stimulus needs positive Sth; when Sth>0, zero and
negative S cannot trigger it. The generator does not use |S|. Without a bound
on Sth, a negative S may exceed the threshold.

`spike_noise_margin` assumes `S + |δ| ≤ Sth` and proves no spike at S+δ.
This is a deterministic margin, not a false-positive probability. No noise
distribution, BER, FPR or action-potential waveform is specified. Spike input
S and adaptation voltage V are independent; subthreshold V does not imply
no spike, and no spike does not imply unchanged G without an additional
bridge between inputs and thresholds.

## A spatial result, not a temporal one

`spatialAmplitude A0 γ x = A0·γ^x`, where x:ℕ counts spatial steps.
For A0≥0 and 0<γ<1, `0 ≤ A(x) ≤ A0` is proved. For A0>0 the function is
`StrictAnti`: x<y implies A(y)<A(x). On a finite chain, x≤L implies A(L)≤A(x).
At A0=0 the profile is zero and strict decrease fails. For A0<0, A(x)≤A0
does not generally hold. γ=0 and γ=1 are excluded from the strict result.
There is no continuous coordinate or real-valued limit theorem as x→∞.

A spatial profile defines no temporal evolution and cannot exclude autonomous
oscillation. Conductance may alternate under opposite external drives while
all bounds hold. Branching, feedback, calcium waves, electro-osmosis,
biochemistry and tissue safety are not defined. No new biological simulation
or experiment was performed. The physical bridge remains open and novelty
is not assessed. Hardware authorization and the Third Obligation are unchanged.

## Proof method

Positive affine coefficients preserve the interval; expansion and `ring`
give the history difference. Threshold results use case analysis and δ≤|δ|.
Powers of 0<γ<1 strictly decrease with their natural exponent; multiplication
by positive A0 preserves strictness. There are no direct Verification imports;
proofs use rational arithmetic and Mathlib's ordered powers.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [conductance_bounds_invariant](../../Verification/FungalMyceliumMemristorContract.lean#L66)
- [potentiation_strict](../../Verification/FungalMyceliumMemristorContract.lean#L80)
- [depression_strict](../../Verification/FungalMyceliumMemristorContract.lean#L84)
- [positive_threshold_active](../../Verification/FungalMyceliumMemristorContract.lean#L97)
- [negative_threshold_active](../../Verification/FungalMyceliumMemristorContract.lean#L100)
- [hysteresis_monotonicity_up](../../Verification/FungalMyceliumMemristorContract.lean#L114)
- [hysteresis_monotonicity_down](../../Verification/FungalMyceliumMemristorContract.lean#L118)
- [subthreshold_stability](../../Verification/FungalMyceliumMemristorContract.lean#L122)
- [history_difference](../../Verification/FungalMyceliumMemristorContract.lean#L126)
- [history_dependence](../../Verification/FungalMyceliumMemristorContract.lean#L132)
- [threshold_history_dependence](../../Verification/FungalMyceliumMemristorContract.lean#L139)
- [common_probe_history](../../Verification/FungalMyceliumMemristorContract.lean#L149)
- [power_eq_current_voltage](../../Verification/FungalMyceliumMemristorContract.lean#L165)
- [power_nonnegative](../../Verification/FungalMyceliumMemristorContract.lean#L168)
- [spike_iff](../../Verification/FungalMyceliumMemristorContract.lean#L173)
- [spike_threshold_inactive](../../Verification/FungalMyceliumMemristorContract.lean#L176)
- [spike_noise_margin](../../Verification/FungalMyceliumMemristorContract.lean#L182)
- [spatial_attenuation_decay](../../Verification/FungalMyceliumMemristorContract.lean#L211)
- [spatial_attenuation_bound](../../Verification/FungalMyceliumMemristorContract.lean#L215)
- [finite_chain_attenuation](../../Verification/FungalMyceliumMemristorContract.lean#L206)
- [verification_suite](../../Verification/FungalMyceliumMemristorContract.lean#L251)

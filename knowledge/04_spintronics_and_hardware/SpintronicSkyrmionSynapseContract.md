---
id: SpintronicSkyrmionSynapseContract
language: en
section: quantum-physics
source: Verification/SpintronicSkyrmionSynapseContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 69dcc25af65936881debd0740bc37259797eee5705c3977f016aeff58b5ef56f
---

# Bounded count and rational synaptic weight

[Section](../quantum-physics/README.md) · [Lean](../../Verification/SpintronicSkyrmionSynapseContract.lean)

Stage ε266. The user-selected model stores a bounded count; weight is its
projection, rather than an independently updated analog state variable.

## Exact contract

`SkyrmionSynapse N` contains `count : ℕ` and a proof of `count ≤ N`.
`weight s : ℚ = (s.count : ℚ)/(N : ℚ)`. For `0 < N`, the module proves
`0 ≤ weight s ∧ weight s ≤ 1`. Capacity and count are dimensionless;
weight is a dimensionless fraction. The definition also returns zero at N=0
through Lean's totalized division; this is not a positive physical capacity.

`classifyCurrent threshold I` uses rational parameters. It selects
`Potentiate` when `threshold ≤ I`; otherwise `Depress` when `I ≤ -threshold`;
otherwise `Subthreshold`. For `threshold > 0`, both endpoints ±threshold
are active, while inactivity is equivalent to `|I| < threshold`.
Positive-branch priority is explicit in the definition; no physical
interpretation is asserted for nonpositive thresholds.

`step Potentiate` maps n to `min N (n+1)`, `step Depress` to natural
subtraction `n-1`, truncated at zero, and `step Subthreshold` preserves the
entire state. `stateUpdate` applies the classified action. The module proves
count boundedness, state and weight invariance inside the strict inactive
band, nondecreasing weight for one positive step and nonincreasing weight
for one negative step when N>0. This compares values before and after a step;
it does not establish a physical drift law.

For k identical classified actions, the exact counts are `min N (n+k)`
for potentiation and natural subtraction `n-k` for depression. Positive
saturation is equivalent to `N-n ≤ k`; negative saturation to `n ≤ k`.
The uniform sufficient dose `N ≤ k` works from every valid state: for N>0,
the positive series reaches count=N and weight=1; the negative series reaches
count=0 and weight=0. The latter formal statement holds even for N=0.
Any finite repetition of `Subthreshold` preserves the state. Here dose
means an event count, not duration or integrated current.

## Disturbances and interpretation limits

`bounded_disturbance_invariance` derives invariance under I+δ from the strict
margin `|I|+|δ| < threshold` using the triangle inequality. Strictness matters:
a threshold-level effective pulse is already active. This is a deterministic
bound on the control argument, not a thermal law, noise distribution or
retention-time estimate. No physical-unit calibration of I or threshold is given.

The invariant `count ≤ N` concerns occupancy. Magnetic-texture topological
charge and its correspondence to the count are neither defined nor proved.
The name skyrmion does not establish topological protection. SOT/STT, LLG,
DMI, Δt, energy barriers, Arrhenius activation, fabrication, physical
non-volatility and thermal device stability are outside this model.

## Model choice and dependencies

The previously discussed independent analog weight with μ·Δt·D(I) was not
implemented: the user selected count/N. The historical specification is
preserved separately from the approved one; the models must not be silently
mixed. There are no direct Verification imports. The proofs use Mathlib's
ordered rationals, natural arithmetic and induction. Novelty is not assessed.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [weight_in_unit_interval](../../Verification/SpintronicSkyrmionSynapseContract.lean#L53)
- [classify_subthreshold_iff](../../Verification/SpintronicSkyrmionSynapseContract.lean#L74)
- [classify_positive_endpoint](../../Verification/SpintronicSkyrmionSynapseContract.lean#L80)
- [classify_negative_endpoint](../../Verification/SpintronicSkyrmionSynapseContract.lean#L83)
- [subthreshold_invariance](../../Verification/SpintronicSkyrmionSynapseContract.lean#L95)
- [step_monotonicity_potentiate](../../Verification/SpintronicSkyrmionSynapseContract.lean#L127)
- [step_monotonicity_depress](../../Verification/SpintronicSkyrmionSynapseContract.lean#L132)
- [repeat_potentiate_count](../../Verification/SpintronicSkyrmionSynapseContract.lean#L137)
- [repeat_depress_count](../../Verification/SpintronicSkyrmionSynapseContract.lean#L146)
- [potentiation_saturated_iff](../../Verification/SpintronicSkyrmionSynapseContract.lean#L167)
- [depression_saturated_iff](../../Verification/SpintronicSkyrmionSynapseContract.lean#L172)
- [saturation_by_dose_potentiate](../../Verification/SpintronicSkyrmionSynapseContract.lean#L177)
- [saturation_by_dose_depress](../../Verification/SpintronicSkyrmionSynapseContract.lean#L186)
- [bounded_disturbance_invariance](../../Verification/SpintronicSkyrmionSynapseContract.lean#L194)
- [verification_suite](../../Verification/SpintronicSkyrmionSynapseContract.lean#L219)

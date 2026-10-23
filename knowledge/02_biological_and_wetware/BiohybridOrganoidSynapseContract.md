---
id: BiohybridOrganoidSynapseContract
language: en
section: quantum-physics
source: Verification/BiohybridOrganoidSynapseContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 153db5c451f061fbb51d445832d195c890e34e9a24c185068d278e62aefd88f3
---

# Rational STDP and an ensemble synaptic-weight budget

[Section](../quantum-physics/README.md) · [Lean](../../Verification/BiohybridOrganoidSynapseContract.lean)

Stage ε270: the requested ε268 and ε269 belong to a parallel stream.
A separate index was reserved. The model prescribes abstract weight updates;
its name does not establish the operation of a living organoid.

## State and prescribed STDP window

`OrganoidSynapseState` stores `weight`, `wMax : ℚ` with proofs of
`0 < wMax`, `0 ≤ weight` and `weight ≤ wMax`. The bounds are closed.
`STDPParameters` contains four strictly positive rational parameters:
`A_plus`, `A_minus`, `tau_plus`, `tau_minus`. The argument is `dt : ℤ`.

For dt>0, `stdpWindow` is `A_plus*tau_plus/(tau_plus+|dt|)`;
for dt<0 it is `−A_minus*tau_minus/(tau_minus+|dt|)`; at dt=0 it is zero.
Here |dt| means `|(dt : ℚ)|`. The denominators are positive.
The positive, negative and zero signs of the window are proved equivalent
to the respective signs of dt. This rational formula is a stipulated
phenomenological rule; no error bound for an exponential approximation
is established. Parameters, weights, dt and budget lack physical unit calibration.

`stdpUpdate` returns `min wMax (max 0 (weight + stdpWindow p dt))`
with the same wMax. It preserves bounds, does not decrease weight for dt>0,
and does not increase it for dt<0. Strict raw-window sign does not imply
strict clamped change: positive input at the cap and negative input at zero
leave the weight unchanged. The claim of being strictly inside the interval
is replaced by the exact closed invariant [0,wMax].

## Common normalization factor

`EnsembleState K := Fin K → OrganoidSynapseState` permits K=0;
components may have different wMax values. `totalWeight` is the finite sum
S≥0. For B≥0, `normalizationFactor` is 1 if S≤B and B/S otherwise.
The division branch has S>0; S=0 takes the first branch, including B=0.

`homeostaticNormalize B hB s` multiplies all weights by that common c.
The proofs establish `0 ≤ c ≤ 1`, `0 ≤ w_i' ≤ w_i ≤ wMax_i`, preserved
wMax values, the exact sum `S' = min S B`, S'≤B, and idempotence.
Normalization is the identity when S≤B. Proportionality is expressed as
cross-products `w_i'·w_j = w_j'·w_i`, avoiding division by zero weights.
At B=0 all weights vanish, so nonzero component ratios are not guaranteed.

Nonnegative B is essential: a nonnegative total, even for an empty ensemble,
cannot be ≤B for B<0. This is a formal weight budget, not ATP, oxygen or
energy expenditure, nor a proof of metabolic sufficiency.

## Silence, simultaneity and composition

`eventUpdate` takes `Option ℤ`: `none` is an absent pair; `some 0` is a
zero-lag pair. These distinct inputs have the same local identity action.
`silence_invariance` concerns only the local `none` case.

`ensembleEventUpdate` acts componentwise; `ensembleStep` then normalizes
the whole ensemble. The budget and each wMax are preserved.
`composite_silence_invariance` requires both absence of all events and
initial `totalWeight s ≤ B`. Without the latter premise, normalization
changes an over-budget ensemble even under complete silence. Local LTP
monotonicity likewise does not guarantee a nondecreasing component after
the global normalization.

## Proof method and limits

Positivity of rational fractions establishes window signs; min/max properties
give bounds and weak monotonicity. Factoring the common multiplier out of
the finite sum and splitting on S≤B gives the exact budget. Idempotence follows
because the first output is within budget. Composite silence follows from
local identity only with the initial budget premise. There are no direct
Verification imports; proofs use rational arithmetic and Mathlib finite sums.

The model does not define membrane dynamics, Hodgkin–Huxley equations,
neurotransmitter diffusion, metabolism, tissue viability, cell death,
epileptiform activity, spike measurement or real temporal causality.
The name homeostatic does not establish physiological homeostasis or tissue
safety. There is no biological simulation or experimental evidence. Novelty
is not assessed; hardware authorization and the Third Obligation are unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [stdp_asymmetry_sign](../../Verification/BiohybridOrganoidSynapseContract.lean#L64)
- [weight_bounds_invariant](../../Verification/BiohybridOrganoidSynapseContract.lean#L86)
- [ltp_monotonicity](../../Verification/BiohybridOrganoidSynapseContract.lean#L91)
- [ltd_monotonicity](../../Verification/BiohybridOrganoidSynapseContract.lean#L96)
- [stdp_zero_identity](../../Verification/BiohybridOrganoidSynapseContract.lean#L101)
- [silence_invariance](../../Verification/BiohybridOrganoidSynapseContract.lean#L112)
- [zero_event_identity](../../Verification/BiohybridOrganoidSynapseContract.lean#L115)
- [normalization_factor_bounds](../../Verification/BiohybridOrganoidSynapseContract.lean#L131)
- [normalized_component_bounds](../../Verification/BiohybridOrganoidSynapseContract.lean#L149)
- [total_after_normalize](../../Verification/BiohybridOrganoidSynapseContract.lean#L163)
- [homeostatic_normalization_bound](../../Verification/BiohybridOrganoidSynapseContract.lean#L172)
- [normalize_if_within_budget](../../Verification/BiohybridOrganoidSynapseContract.lean#L177)
- [normalization_idempotent](../../Verification/BiohybridOrganoidSynapseContract.lean#L184)
- [normalization_cross_ratio](../../Verification/BiohybridOrganoidSynapseContract.lean#L189)
- [ensemble_budget_bound](../../Verification/BiohybridOrganoidSynapseContract.lean#L203)
- [ensemble_wMax](../../Verification/BiohybridOrganoidSynapseContract.lean#L208)
- [composite_silence_invariance](../../Verification/BiohybridOrganoidSynapseContract.lean#L220)
- [verification_suite](../../Verification/BiohybridOrganoidSynapseContract.lean#L255)

---
id: QuantumDiamondNVInterfaceContract
language: en
section: quantum-physics
source: Verification/QuantumDiamondNVInterfaceContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 473f35b48666e79f7cd240e409e7a426c24e46dd7c7541a1f819b5169833e35e
---

# Diamond NV interface: populations, signal and an ideal π pulse

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumDiamondNVInterfaceContract.lean)

Stage ε267 separates rational populations of three states, an affine response,
and complex amplitudes of an ideal microwave operator. It is a mathematical
contract, not a calibration of a physical NV centre.

## Exact definitions and premises

`NVSpinState` contains `Zero`, `Plus`, `Minus`. `NVSpinPopulation` stores
`p0`, `pPlus`, `pMinus : ℚ`, nonnegativity proofs and a sum of 1.
These dimensionless populations do not themselves encode relative phases
or coherence. `residual p = pPlus + pMinus`.

`opticalPumpStep η hη p` requires a proof of `0 ≤ η ∧ η ≤ 1`.
The step is `p0' = p0 + η·(pPlus+pMinus)`,
`pPlus' = (1−η)·pPlus`, `pMinus' = (1−η)·pMinus`.
Population bounds and nondecreasing p0 are proved. After k `pumpCycles`:
`Rk = (1−η)^k R0`, `p0k = 1−(1−η)^k R0`.
Despite its name, `optical_pump_convergence` is the exact finite residual
formula. A separate `optical_pump_asymptotic_limit` proves p0k → 1
in ℝ for `0 < η ≤ 1`.

At η=0 the step is the identity; at η=1 one step yields pure `Zero`.
For η<1 and R0>0 the residual remains strictly positive after every finite
number of steps, hence p0k<1. Asymptotic polarization does not establish
exact initialization in finitely many cycles. Cycle durations are unspecified.

## Luminescence and the strictness correction

`luminescenceYield r0 r_dark p = r_dark + (r0−r_dark)·p0`.
The response difference is `(r0−r_dark)·(q.p0−p.p0)`.
For `r_dark ≤ r0`, a weak increase in p0 gives a weak signal increase.
For `r_dark < r0`, a strict signal increase is equivalent to a strict
increase in p0; equal populations cannot yield a strict response increase.
The bounds `r_dark ≤ L ≤ r0` are proved. Nonnegativity additionally needs
`0 ≤ r_dark` and `r_dark ≤ r0`. Positive contrast and R0>0 give a response
strictly below that of pure `Zero`.

The rates r0 and r_dark are not calibrated in photons/s or other physical
units. No universal ODMR dip is proved: the π permutation may decrease
or increase p0; from pure `Minus` it raises p0 to 1. This follows from the
prescribed formulas and is not a measured device spectrum.

## Complex operator and population bridge

`mwPiPulseStep` swaps p0 and pMinus while retaining pPlus; two steps restore
the populations. For `CoherentAmp := ℂ × ℂ × ℂ` in Zero, Plus, Minus order,
`coherentPi(a0,aPlus,aMinus) = (−i·aMinus,aPlus,−i·a0)`.
The proofs establish complex linearity, both identities for an explicit
inverse, preservation of `ampIntensity = |a0|²+|aPlus|²+|aMinus|²`, and
preservation of that quantity for amplitude differences. These are properties
of a concrete operator, rather than a value of a packaged `Unitary` type.

Two applications yield `(-a0,aPlus,-aMinus)`. This is not the amplitude
identity and does not generally reduce to one global phase. `Represents a p`
separately assumes that each `Complex.normSq` equals the corresponding
rational population embedded into ℝ. Under this premise, normalization and
compatibility of the complex operator with the population permutation are
proved. No universal conversion of arbitrary complex amplitudes into exact
rational populations is asserted.

## Scope

532 nm, the S1 triplet and intersystem crossing ISC motivate the model;
their full dynamics are not defined. There is no theorem of nondemolition
readout, coherence preservation during pumping or measurement, Lindblad
dynamics, thermal behaviour, T2, crystal preservation, fabrication or physical
calibration. There are no direct Verification imports. The proofs use rational
arithmetic, complex norms and Mathlib's geometric limit. Novelty is not
assessed. Hardware authorization and the Third Obligation are unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [population_bounds](../../Verification/QuantumDiamondNVInterfaceContract.lean#L42)
- [optical_pump_p0_monotonicity](../../Verification/QuantumDiamondNVInterfaceContract.lean#L75)
- [optical_pump_convergence](../../Verification/QuantumDiamondNVInterfaceContract.lean#L85)
- [optical_pump_p0_exact](../../Verification/QuantumDiamondNVInterfaceContract.lean#L92)
- [finite_p0_lt_one](../../Verification/QuantumDiamondNVInterfaceContract.lean#L120)
- [optical_pump_asymptotic_limit](../../Verification/QuantumDiamondNVInterfaceContract.lean#L128)
- [luminescence_difference](../../Verification/QuantumDiamondNVInterfaceContract.lean#L156)
- [readout_contrast_monotonicity](../../Verification/QuantumDiamondNVInterfaceContract.lean#L162)
- [readout_contrast_strict_mono](../../Verification/QuantumDiamondNVInterfaceContract.lean#L169)
- [luminescence_nonneg](../../Verification/QuantumDiamondNVInterfaceContract.lean#L188)
- [mw_pi_pulse_involution](../../Verification/QuantumDiamondNVInterfaceContract.lean#L209)
- [coherent_pi_add](../../Verification/QuantumDiamondNVInterfaceContract.lean#L224)
- [coherent_pi_smul](../../Verification/QuantumDiamondNVInterfaceContract.lean#L229)
- [coherent_pi_intensity](../../Verification/QuantumDiamondNVInterfaceContract.lean#L234)
- [coherent_pi_inverse_left](../../Verification/QuantumDiamondNVInterfaceContract.lean#L238)
- [coherent_pi_inverse_right](../../Verification/QuantumDiamondNVInterfaceContract.lean#L243)
- [coherent_pi_twice](../../Verification/QuantumDiamondNVInterfaceContract.lean#L249)
- [coherent_pi_difference_intensity](../../Verification/QuantumDiamondNVInterfaceContract.lean#L255)
- [represents_normalized](../../Verification/QuantumDiamondNVInterfaceContract.lean#L265)
- [coherent_pi_population_bridge](../../Verification/QuantumDiamondNVInterfaceContract.lean#L271)
- [verification_suite](../../Verification/QuantumDiamondNVInterfaceContract.lean#L304)

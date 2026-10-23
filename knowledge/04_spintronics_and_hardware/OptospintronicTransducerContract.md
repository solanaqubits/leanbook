---
id: OptospintronicTransducerContract
language: en
section: quantum-physics
source: Verification/OptospintronicTransducerContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 47f43ff50de91774cfd220db9566116e65372c68bc95c11d51d47ca69ce75bfa
---

# Mean optical angular momentum and a bounded spin reservoir

[Section](../quantum-physics/README.md) · [Lean](../../Verification/OptospintronicTransducerContract.lean)

Stage ε274: requested ε272 is occupied along with ε273 by a parallel stream.
This is a scalar mean-transfer contract with explicit remainder accounting;
it does not derive a physical optospintronic conversion mechanism.

## Exact objects and normalization

`OpticalPolarization` has `LeftCircular`, `RightCircular`, `Linear`.
`polarizationSign` assigns −1,+1,0 respectively along a chosen axis.
`OpticalPulse` stores `photonCount : ℕ`, `polarization`, `couplingEfficiency : ℚ` with 0≤η≤1,
where η denotes couplingEfficiency.
`SpinReservoirState Smax` has Smax:ℕ, including zero, and `spinZ : ℚ`
satisfying −Smax≤s≤Smax after casting capacity into ℚ. Moments are normalized
to ħ; no numerical value of the physical constant is supplied.

`couplingBudget = (n:ℚ)·η = b`, with 0≤b≤n proved.
`momentumDelta s pulse` is min(b,Smax−s) for right polarization,
−min(b,s+Smax) for left polarization, and zero for linear polarization.
`transferMomentum pulse s` returns s′=s+Δ with the same capacity.
The minimum limits transfer by both the budget and available capacity.

The six requested properties are: linear polarization preserves state;
right polarization does not decrease s, left does not increase s;
|s′−s|≤nη; reservoir bounds are preserved; and η=0 gives the identity.
Monotonicity is weak: saturation may produce Δ=0 despite nη>0.
Identity for n=0 and Smax=0 is also proved. With sufficient available capacity,
the entire ±b is transferred, including exact equality at the boundary.
No separate injection threshold is specified; saturation is not a depinning model.

## Complete signed accounting

Write σ=polarizationSign, J=σn, Q=σnη, U=σn(1−η), B=Q−Δ.
The definitions `signedIncidentMomentum`, `requestedMomentum`,
`uncoupledMomentum`, `saturationRemainder` implement these quantities.
`opticalOutputMomentum = U+B`. The chosen model retains both uncoupled and
saturation-blocked parts in the optical sector.

The proofs give Jout=J−Δ and `s+J=s′+Jout`. This follows algebraically
from the prescribed allocation; it is not an independent QED or STT derivation.
For right polarization, 0≤B≤b and 0≤Jout≤n; for left polarization,
−b≤B≤0 and −n≤Jout≤0. For linear polarization B=Jout=0; in general |Jout|≤n.
Remainders are signed projections, not nonnegative intensities, energies or
outgoing photon counts. For n=2,η=1,s=0,Smax=1, right polarization transfers
1 and leaves Jout=1: omitting the remainder would break the claimed balance.

## A mean is not integer event transfer

For n=1,η=1/2,s=0,Smax=1, right polarization yields Δ=1/2.
Even η=1 does not ensure integrality when the initial s is rational and
saturation occurs. No random absorbed-photon count, variance, measurement
or discrete-outcome distribution is specified.
`Linear` means zero mean projection: unchanged s and scalar Jout=0 do not
imply absent light or zero individual-photon spin. At η=0, no transfer does
not mean the input disappears: the balance gives Jout=J.

## Proof methods and open bridges

The nonnegative minimum is bounded by budget and available capacity;
polarization cases give direction and reservoir invariance. J=Q+U and
Q=Δ+B close the balance; signed output bounds are proved separately.
There are no direct Verification imports; proofs use rational arithmetic,
min/max and Mathlib algebra.

There is no spectrum, monochromaticity condition, temporal relaxation,
spin-orbit scattering, microscopic STT dynamics, thermal balance or device
realization. Registering the suite does not establish a physical bridge
between an MZI, this reservoir and a skyrmion count. Angular-momentum
conservation is not an energy-conservation proof for a device. Novelty is
not assessed; there is no publication, hardware/authorization change or
change to the Third Obligation.

The incoming ε271 summary is separately corrected: its actual spike threshold
is strict S>Sth, not S≥Sth. That module is unchanged; this is not a new
injection threshold.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [coupling_budget_nonnegative](../../Verification/OptospintronicTransducerContract.lean#L40)
- [coupling_budget_le_count](../../Verification/OptospintronicTransducerContract.lean#L43)
- [actual_transfer_eq_delta](../../Verification/OptospintronicTransducerContract.lean#L88)
- [saturation_bound_invariant](../../Verification/OptospintronicTransducerContract.lean#L92)
- [linear_polarization_invariance](../../Verification/OptospintronicTransducerContract.lean#L97)
- [right_polarization_monotonicity](../../Verification/OptospintronicTransducerContract.lean#L102)
- [left_polarization_monotonicity](../../Verification/OptospintronicTransducerContract.lean#L107)
- [transferred_momentum_bound](../../Verification/OptospintronicTransducerContract.lean#L112)
- [zero_efficiency_neutrality](../../Verification/OptospintronicTransducerContract.lean#L130)
- [zero_photon_identity](../../Verification/OptospintronicTransducerContract.lean#L135)
- [zero_capacity_identity](../../Verification/OptospintronicTransducerContract.lean#L139)
- [right_unsaturated_transfer](../../Verification/OptospintronicTransducerContract.lean#L148)
- [left_unsaturated_transfer](../../Verification/OptospintronicTransducerContract.lean#L154)
- [optical_output_eq_incident_sub_delta](../../Verification/OptospintronicTransducerContract.lean#L180)
- [angular_momentum_conservation](../../Verification/OptospintronicTransducerContract.lean#L187)
- [right_remainder_bounds](../../Verification/OptospintronicTransducerContract.lean#L193)
- [left_remainder_bounds](../../Verification/OptospintronicTransducerContract.lean#L200)
- [linear_remainder_zero](../../Verification/OptospintronicTransducerContract.lean#L207)
- [right_output_bounds](../../Verification/OptospintronicTransducerContract.lean#L213)
- [left_output_bounds](../../Verification/OptospintronicTransducerContract.lean#L223)
- [optical_output_magnitude_bound](../../Verification/OptospintronicTransducerContract.lean#L233)
- [verification_suite](../../Verification/OptospintronicTransducerContract.lean#L262)

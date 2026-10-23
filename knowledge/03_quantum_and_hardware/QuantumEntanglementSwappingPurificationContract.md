---
id: QuantumEntanglementSwappingPurificationContract
language: en
section: quantum-physics
source: Verification/QuantumEntanglementSwappingPurificationContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 26dfbf25fcdcfb7d447f229ef46b717e4e1a141e6e3f5f060e456c98049a25d6
---

# Ideal swapping and conditional binary Bell-error filtering

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumEntanglementSwappingPurificationContract.lean)

Stage ε280 separates swapping of two ideal pairs from independent phase-label
filtering. Placing them in one module does not establish an end-to-end noisy
repeater model. Novelty is not assessed.

## Four qubits and projection on BC

`FourKet` has four Fin 2 indices ordered A,B,C,D. `swappingInput` is Φ+AB⊗Φ+CD.
Bell kets and corrections are reused from
[QuantumStateAvailabilityContract](QuantumStateAvailabilityContract.md).
`swappingContraction` sums over B,C against the conjugated Bell ket;
`swappingProject` restores the selected Bell factor on BC.

The contraction is proved to equal half of the same Bell ket on AD, and the
projection equals half of `normalizedSwap`. All four projections sum to the
source. `swappedOuter` is the corresponding normalized Bell ket. `correctOuter`
applies the correction matching the actual outcome on D and exactly yields Φ+AD.
The Ψ− sign follows from this particular subsystem ordering; the inverse ZX
correction is used, rather than unconditionally repeating XZ.

The source squared norm is 1. Each selected branch has Born weight 1/4 and all
four weights sum to 1. This assumes a complete ideal Bell measurement and the
correct classical outcome, not a real detector registration rate. A nonzero
determinant excludes every product of two single-qubit vectors, proving actual
entanglement rather than merely correlation.

`outerReduced` is a finite partial trace over BC. For the normalized conditional
state it equals the rank-one density of the selected Bell ket and has trace 1.
`purePairDensity` is positive semidefinite for every ket.

## A restricted density family

`phaseDensity F = F |Φ+><Φ+| + (1−F)|Φ−><Φ−|`, with rational F.
For 0≤F≤1, `Matrix.PosSemidef` and Hermiticity are proved; the trace is 1.
`targetOverlap` explicitly computes <Φ+|ρ|Φ+> and equals F embedded in ℂ.
For this normalized pure target it is the usual squared-fidelity overlap;
a general fidelity formula for two mixed states is not implemented.
Only Φ+ and Φ− occur: this is not general Werner/Bell-diagonal noise.
F measures overlap with the chosen Φ+, not entanglement: F=0 gives the entangled
Bell state Φ−. At F=1/2 the matrix is the equal mixture of |00><00| and |11><11|;
this is an algebraic reading of this mixture, not a general entanglement monotone.

## Conditional purification and correction of the request

Two Bool labels are independent, with joint weights given by products of F
and 1−F. Nonnegativity on [0,1], total mass 1 and the stated marginal weights
are proved. The filter accepts equal labels and retains their common value.
Finite sums yield acceptedGoodMass=F², acceptedBadMass=(1−F)² and
`p=acceptedMass=F²+(1−F)²`. On [0,1] the acceptance probability lies in [1/2,1].
The posterior normalizes the actual acceptedGoodMass, giving
`F'=purifiedFidelity F=F²/p`. `filteredDensity` is constructed from all four joint
weights and equality acceptance. It equals `phaseDensity F'`, is positive
semidefinite, has unit trace and targetOverlap=F'. This establishes the chosen
label filter, not a BBPSSW/Deutsch/CNOT/LOCC circuit or physical label measurement.

The signed identity `F'−F=F(1−F)(2F−1)/p` proves strict improvement precisely
when 1/2<F<1 within [0,1]. The points 0,1/2,1 are fixed and are all rational
fixed points. At F=1 strict improvement contradicts the upper bound 1.
Denominator positivity and 0≤F'≤1 hold algebraically for every rational F;
this does not turn negative input weights outside [0,1] into probabilities.

The originally supplied formula is retained as `rejectedFormula`:
`g(F)=(F²+(1−F)³/3)/(F²+2F(1−F)+(5/3)(1−F)²)`.
Exact counterexamples prove g(0)=1/5 and g(3/4)=109/200<3/4, refuting the original
requirements. The explicitly permitted simpler model is used openly; the original
formula has not silently been proved. Acceptance cost and two input labels are
separate from conditional fidelity: there is no free deterministic improvement
of an unknown state.

Independence matters: perfectly correlated equal labels with the same marginal F
always pass and retain F without improvement. This counterexample does not expand
the independent model. Finite exact purification to F=1, iterative convergence,
pairs per second and physical-channel performance are not claimed.

## Scope and previous models

[PhotonicsQuantumTeleportation](../03_quantum_physics_and_optics/PhotonicsQuantumTeleportation.md)
remains a distinct scenario: its passive optical instrument has total postselected
success 1/2. The new ideal all-outcomes result does not raise this to 100%.
That source supplies scope comparison and is not a direct import.

Resource preparation, a physical NV bridge, authenticated outcomes, repeater
noise/loss, detector calibration, delays and hardware safety are not proved.
The only direct project import is QuantumStateAvailabilityContract; its imported
closure is not a collection of new ε280 results. Publication, authorization,
hardware access and the Third Obligation are unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [swapping_contraction_formula](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L59)
- [swapping_projection_formula](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L66)
- [actual_normalized_projection](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L104)
- [normalized_swap_norm](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L101)
- [swapped_outer_eq_bell](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L73)
- [swapping_exact_correction](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L77)
- [swapping_canonical_decomposition](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L83)
- [bell_pair_normalized](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L95)
- [swapping_input_normalized](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L98)
- [swapping_success_probability](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L112)
- [all_outcomes_success](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L116)
- [bell_not_product](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L126)
- [swapping_target_entanglement](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L135)
- [swapped_outer_density](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L154)
- [swapped_density_trace_one](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L164)
- [rejected_formula_counterexamples](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L172)
- [joint_weights_sum](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L184)
- [joint_weights_nonnegative](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L188)
- [independent_marginal](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L193)
- [accepted_mass_formula](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L197)
- [accepted_mass_positive](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L206)
- [purification_success_bounds](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L210)
- [purification_posterior_formula](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L220)
- [purification_bounds_invariant](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L224)
- [purification_difference](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L231)
- [purification_strict_improvement](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L239)
- [purification_improvement_iff](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L247)
- [fixed_points_purification](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L261)
- [purification_fixed_iff](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L265)
- [phase_density_positive](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L295)
- [phase_density_hermitian](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L301)
- [phase_density_trace](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L304)
- [phase_density_fidelity](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L311)
- [filtered_density_formula](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L325)
- [filtered_density_valid](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L339)
- [verification_suite](../../Verification/QuantumEntanglementSwappingPurificationContract.lean#L374)

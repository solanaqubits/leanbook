import Verification.QuantumLocalNoisySwapping

noncomputable section
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGeneralBellReadout (Readout)
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoisyVisibility QuantumLocalPostNoise
open QuantumLocalNoisySwapping
open scoped BigOperators ComplexOrder Matrix

-- No separability, positivity or normalization restriction in the marginal identity.
example {κ : Type} [Fintype κ] (E : CPTP (Fin 2) κ) (M : PairDensity) :
    traceD ((onD E).map M) = traceD M := onD_preserves_A E M

-- Local CP is tested under a nontrivial ancilla, not just on unextended states.
example (g : Visibility) (R : Matrix (Fin 2 × PairIndex) (Fin 2 × PairIndex) ℂ)
    (hR : R.PosSemidef) :
    (Matrix.of fun (a b : Fin 2 × PairIndex) =>
      (localDepolarizing g).map (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2).PosSemidef :=
  (localDepolarizing g).cp 2 R hR

-- The existing branch and rejection trace contract survives local-D post-noise.
example {κ : Type} [Fintype κ] (pre : CPTP FourIndex κ)
    (g : BellMeasurement → Visibility) (model : Readout) (ρ : FourState) (o : Outcome) :
    (noisyOutcome pre (fun r => localDepolarizing (g r)) model o ρ.matrix).trace.re =
      outcomeProbability model o (noiseState pre ρ) := noisy_probability _ _ _ _ _

example {κ : Type} [Fintype κ] (pre : CPTP FourIndex κ)
    (g : BellMeasurement → Visibility) (model : Readout) (ρ : FourState) :
    (∑ o : Outcome,
      noisyOutcome pre (fun r => localDepolarizing (g r)) model o ρ.matrix).trace = 1 := by
  rw [noisy_total_trace, ρ.trace_one]

-- Agreement holds also for subnormalized complex Bell-projector combinations.
example (g : Visibility) (c : BellMeasurement → ℂ) :
    (localDepolarizing g).map (∑ a, c a • QuantumNoisyBellInstrument.bellProjector a) =
      (depolarizing g).map (∑ a, c a • QuantumNoisyBellInstrument.bellProjector a) :=
  local_equals_pair_on_bell_mixture g c

def one : Visibility := ⟨1, by norm_num, by norm_num⟩
def zero : Visibility := ⟨0, by norm_num, by norm_num⟩
def half : Visibility := ⟨1/2, by norm_num, by norm_num⟩

example : targetOverlap (localNoisyWernerOutput half half half half) = (19/64 : ℂ) := by
  rw [local_noisy_visibility_fidelity]
  norm_num [half]

example : targetOverlap (localNoisyWernerOutput one one half half) = (7/16 : ℂ) := by
  rw [local_noisy_visibility_fidelity]
  norm_num [half, one]

example (bsm w v : Visibility) :
    targetOverlap (localNoisyWernerOutput bsm zero w v) = (1/4 : ℂ) := by
  rw [local_noisy_visibility_fidelity]
  norm_num [zero]

-- Both maps are physical on this counterexample, yet they are different maps.
example : productZero.PosSemidef ∧ productZero.trace = 1 ∧
    (localDepolarizing zero).map productZero ≠ (depolarizing zero).map productZero :=
  ⟨product_zero_positive, product_zero_trace,
    local_and_pair_noise_differ_on_product zero (by norm_num [zero])⟩

example : (localDepolarizing zero).map productZero (1,0) (1,0) = 0 ∧
    (depolarizing zero).map productZero (1,0) (1,0) = (1/4 : ℂ) := by
  constructor
  · rw [local_depolarizing_entry]
    norm_num [zero, productZero, traceD, Matrix.diagonal, Fin.sum_univ_two]
  · rw [depolarizing_map, product_zero_trace]
    norm_num [zero]

-- The strict γ<1 hypothesis in the equivalence must not exclude the identity endpoint.
example : (localDepolarizing one).map productZero = (depolarizing one).map productZero ∧
    traceD productZero ≠ (productZero.trace/2) • (1 : QubitMatrix) := by
  have h := identity_endpoint_agrees one rfl productZero
  exact ⟨h.1.trans h.2.symm, product_zero_marginal_not_mixed⟩

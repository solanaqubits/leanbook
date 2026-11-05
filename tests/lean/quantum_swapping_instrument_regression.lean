import Verification.QuantumSwappingInstrument

open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellCircuitRefinement QuantumNoisyBellInstrument
open QuantumGeneralBellReadout QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumSwappingInstrument
open scoped BigOperators ComplexOrder Matrix

-- The rectangular operator reproduces amplitudes, not only a scalar fidelity.
example (m r : BellMeasurement) (v : FourKet) :
    branchOperator m r *ᵥ flattenFour v = flattenPair (correctOuter r (readoutBranch m v)) :=
  branch_amplitudes m r v

-- CP is checked on an entangled ancillary block, with no separability premise.
example (model : Readout)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (hR : R.PosSemidef) :
    (extension 2 model R).PosSemidef := completely_positive 2 model R hR

-- Full detection with maximally biased classical reports remains trace preserving.
example (M : FourDensity) :
    (acceptedMap (QuantumSelectiveSwapping.biasedReadout false) M).trace = M.trace := by
  apply trace_preserving_full_detection
  intro m
  rfl

-- Coherent off-diagonal entries survive into the input: this is not a classical mixture.
example : ghzState.matrix ((0,0),(0,0)) ((1,1),(1,1)) = (1 / 2 : ℂ) := by
  norm_num [ghzState, pureFourDensity, flattenFour, ghzKet, Matrix.vecMulVec,
    ← pow_two, bellCoeff_sq]

example : bornProbability .phiPlus ghzState ≠ (1 / 4 : ℝ) := by
  rw [ghz_born_probabilities]
  norm_num

example : bornProbability .psiMinus ghzState = 0 := ghz_born_probabilities .psiMinus

example : acceptanceProbability (QuantumSelectiveSwapping.biasedReadout true) ghzState ≠
    QuantumSelectiveSwapping.acceptedMass (QuantumSelectiveSwapping.biasedReadout true) := by
  rw [ghz_acceptance_not_uniform_average.1, ghz_acceptance_not_uniform_average.2]
  norm_num

example (model : Readout) (ρ : FourState) :
    (acceptedMap model ρ.matrix).trace.re + (lostMap model ρ.matrix).trace.re = 1 := by
  have h := congrArg Complex.re (trace_balance model ρ.matrix)
  simpa [ρ.trace_one] using h

example (model : Readout) (ρ : FourState) (h : 0 < acceptanceProbability model ρ) :
    (conditionalState model ρ h).matrix.PosSemidef ∧
    (conditionalState model ρ h).matrix.trace = 1 :=
  ⟨(conditionalState model ρ h).positive, (conditionalState model ρ h).trace_one⟩

example (model : Readout) (p q : BellDistribution) :
    acceptedMap model (inputDensity p q) =
      QuantumBellDiagonalSwapping.acceptedDensity p q model :=
  bell_diagonal_refinement model p q

-- At full detection every valid isotropic product input has acceptance probability one.
example (w v : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    acceptanceProbability QuantumBellDiagonalSwapping.perfectReadout
      (bellInputState (QuantumBellDiagonalSwapping.isotropicDistribution w hw)
        (QuantumBellDiagonalSwapping.isotropicDistribution v hv)) = 1 := by
  unfold acceptanceProbability
  rw [trace_preserving_full_detection _ (by intro m; rfl)]
  simp [FourState.trace_one]

example (model : Readout) (ρ : FourState)
    (hz : acceptanceProbability model ρ = 0) (hp : 0 < acceptanceProbability model ρ) : False := by
  linarith

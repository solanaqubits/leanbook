import Verification.QuantumEntanglementSwappingPurificationContract

open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open scoped BigOperators ComplexOrder
noncomputable section

example : fourNormSq swappingInput = 1 := swapping_input_normalized
example (m : BellMeasurement) : fourNormSq (normalizedSwap m) = 1 := normalized_swap_norm m
example (m : BellMeasurement) :
    (2 : ℂ) • swappingProject m swappingInput = normalizedSwap m := actual_normalized_projection m
example : swapOutcomeProbability .phiPlus = 1 / 4 := swapping_success_probability _
example : swapOutcomeProbability .phiMinus = 1 / 4 := swapping_success_probability _
example : swapOutcomeProbability .psiPlus = 1 / 4 := swapping_success_probability _
example : swapOutcomeProbability .psiMinus = 1 / 4 := swapping_success_probability _
example : swapOutcomeProbability .phiPlus + swapOutcomeProbability .phiMinus +
    swapOutcomeProbability .psiPlus + swapOutcomeProbability .psiMinus = 1 := all_outcomes_success
example : swappingContraction .psiMinus swappingInput 0 1 = (1 / 2 : ℂ) * bellCoeff := by
  rw [swapping_contraction_formula]
  simp [bellKet]
example : swappingContraction .psiMinus swappingInput 1 0 = -(1 / 2 : ℂ) * bellCoeff := by
  rw [swapping_contraction_formula]
  simp [bellKet]
example : correctOuter .psiMinus (swappedOuter .psiMinus) = bellKet .phiPlus :=
  swapping_exact_correction _
example (m : BellMeasurement) : ¬ ∃ u v : QubitState,
    correctOuter m (swappedOuter m) = fun a d => amp u a * amp v d :=
  (swapping_target_entanglement m).2
example (m : BellMeasurement) : (outerReduced (normalizedSwap m)).trace = 1 :=
  swapped_density_trace_one m
example : (outerReduced (normalizedSwap .psiMinus)) (0, 1) (1, 0) = -1 / 2 := by
  rw [swapped_outer_density]
  simp [purePairDensity, Matrix.vecMulVec, bellKet]
  ring_nf
  norm_num [bellCoeff_sq]
-- Applying ZX to the first endpoint instead of D introduces the wrong global sign.
example : amp (applyCorrection .psiMinus (bellKet .psiMinus 0 0, bellKet .psiMinus 1 0)) 0 =
    -bellCoeff := by simp [amp, applyCorrection, bellKet]
example : -bellCoeff ≠ bellCoeff := by
  intro h
  have hz : bellCoeff = 0 := by linear_combination -h / 2
  exact bellCoeff_ne_zero hz
example : rejectedFormula 0 = 1 / 5 := rejected_formula_counterexamples.1
example : rejectedFormula 0 ≠ 0 := by norm_num [rejectedFormula]
example : rejectedFormula (3 / 4) = 109 / 200 := rejected_formula_counterexamples.2.1
example : rejectedFormula (3 / 4) < 3 / 4 := rejected_formula_counterexamples.2.2
example : independentWeight (3 / 4) false false = 9 / 16 := by
  norm_num [independentWeight, labelWeight]
example : independentWeight (3 / 4) false true = 3 / 16 := by
  norm_num [independentWeight, labelWeight]
example : independentWeight (3 / 4) true false = 3 / 16 := by
  norm_num [independentWeight, labelWeight]
example : independentWeight (3 / 4) true true = 1 / 16 := by
  norm_num [independentWeight, labelWeight]
example : acceptedMass (3 / 4) = 5 / 8 := by rw [accepted_mass_formula]; norm_num
example : acceptedGoodMass (3 / 4) = 9 / 16 := by rw [good_mass_formula]; norm_num
example : acceptedBadMass (3 / 4) = 1 / 16 := by rw [bad_mass_formula]; norm_num
example : purifiedFidelity (3 / 4) = 9 / 10 := by rw [purification_posterior_formula]; norm_num
example : (3 / 4 : ℚ) < purifiedFidelity (3 / 4) :=
  purification_strict_improvement _ (by norm_num)
example : purifiedFidelity (1 / 4) = 1 / 10 := by rw [purification_posterior_formula]; norm_num
example : purifiedFidelity (1 / 4) < 1 / 4 := by rw [purification_posterior_formula]; norm_num
example : purifiedFidelity 0 = 0 := fixed_points_purification.1
example : purifiedFidelity (1 / 2) = 1 / 2 := fixed_points_purification.2.1
example : purifiedFidelity 1 = 1 := fixed_points_purification.2.2
example : ¬ (1 : ℚ) < purifiedFidelity 1 := by rw [fixed_points_purification.2.2]; norm_num
example : acceptedMass 0 = 1 := by rw [accepted_mass_formula]; norm_num
example : acceptedMass (1 / 2) = 1 / 2 := by rw [accepted_mass_formula]; norm_num
example : acceptedMass 1 = 1 := by rw [accepted_mass_formula]; norm_num
example : purificationStep (3 / 4) (by norm_num) = 9 / 10 := by
  rw [purificationStep, purification_posterior_formula]; norm_num
example : (phaseDensity (3 / 4)).PosSemidef := phase_density_positive _ (by norm_num)
example : (phaseDensity (3 / 4)).IsHermitian := phase_density_hermitian _ (by norm_num)
example : (phaseDensity (3 / 4)).trace = 1 := phase_density_trace _
example : targetOverlap (phaseDensity (3 / 4)) = 3 / 4 := by
  rw [phase_density_fidelity]; norm_num
example : targetOverlap (filteredDensity (3 / 4)) = 9 / 10 := by
  rw [(filtered_density_valid _).2.2, purification_posterior_formula]; norm_num
example : (filteredDensity (3 / 4)).trace = 1 := (filtered_density_valid _).2.1
-- The balanced phase mixture is a diagonal classical mixture, not a pure entangled state.
example : phaseDensity (1 / 2) (0, 0) (1, 1) = 0 := by
  simp [phaseDensity, purePairDensity, Matrix.vecMulVec, bellKet, Complex.real_smul]
  ring
example : phaseDensity (1 / 2) (0, 0) (0, 0) = 1 / 2 := by
  simp [phaseDensity, purePairDensity, Matrix.vecMulVec, bellKet, Complex.real_smul]
  ring_nf
  norm_num [bellCoeff_sq]
-- The raw joint law is a probability distribution only in the declared parameter domain.
example : independentWeight (-1) false true = -2 := by norm_num [independentWeight, labelWeight]
private def correlatedWeight (F : ℚ) (a b : Bool) : ℚ := if a = b then labelWeight F a else 0
private def correlatedSuccess (F : ℚ) : ℚ :=
  ∑ a : Bool, ∑ b : Bool, if a = b then correlatedWeight F a b else 0
private def correlatedGood (F : ℚ) : ℚ :=
  ∑ a : Bool, ∑ b : Bool, if a = false ∧ a = b then correlatedWeight F a b else 0
example : correlatedSuccess (3 / 4) = 1 := by
  norm_num [correlatedSuccess, correlatedWeight, labelWeight]
example : correlatedGood (3 / 4) / correlatedSuccess (3 / 4) = 3 / 4 := by
  norm_num [correlatedGood, correlatedSuccess, correlatedWeight, labelWeight]
example : correlatedGood (3 / 4) / correlatedSuccess (3 / 4) < purifiedFidelity (3 / 4) := by
  rw [purification_posterior_formula]
  norm_num [correlatedGood, correlatedSuccess, correlatedWeight, labelWeight]
example : (∑ a : Bool, ∑ b : Bool,
    if a = b then (if a ≠ b then (1 / 2 : ℚ) else 0) else 0) = 0 := by simp
example : QuantumEntanglementSwappingPurificationSuite := verification_suite

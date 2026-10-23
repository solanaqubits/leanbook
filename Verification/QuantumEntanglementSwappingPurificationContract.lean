/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumStateAvailabilityContract
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FieldSimp

/-!
# Ideal entanglement swapping and an independent binary phase-label filter

The four-qubit projection is a complete ideal Bell measurement. The purification
model filters equal labels from two independent binary Bell-phase mixtures. It is
not a CNOT circuit, a Werner-state protocol or a physical detector implementation.
The supplied rational formula and its false strict/end-point claims are rejected explicitly.
-/
namespace QuantumEntanglementSwappingPurificationContract

noncomputable section
open scoped BigOperators ComplexOrder
open QuantumStateAvailabilityContract

abbrev FourKet := Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ
abbrev PairIndex := Fin 2 × Fin 2
abbrev PairDensity := Matrix PairIndex PairIndex ℂ

theorem bellCoeff_cube : bellCoeff ^ 3 = bellCoeff * (1 / 2 : ℂ) := by
  rw [pow_succ, bellCoeff_sq]
  ring

theorem bellCoeff_four : bellCoeff ^ 4 = (1 / 4 : ℂ) := by
  calc
    _ = (bellCoeff ^ 2) ^ 2 := by ring
    _ = _ := by rw [bellCoeff_sq]; norm_num

theorem bellCoeff_ne_zero : bellCoeff ≠ 0 := by
  intro h
  have hh := bellCoeff_sq
  rw [h] at hh
  norm_num at hh

def swappingInput : FourKet := fun a b c d => bellKet .phiPlus a b * bellKet .phiPlus c d

def swappingContraction (m : BellMeasurement) (v : FourKet) : PairKet := fun a d =>
  ∑ b, ∑ c, star (bellKet m b c) * v a b c d

def swappingProject (m : BellMeasurement) (v : FourKet) : FourKet := fun a b c d =>
  bellKet m b c * swappingContraction m v a d

def normalizedSwap (m : BellMeasurement) : FourKet := fun a b c d =>
  bellKet m b c * bellKet m a d

def swappedOuter (m : BellMeasurement) : PairKet := (2 : ℂ) • swappingContraction m swappingInput

def correctOuter (m : BellMeasurement) (v : PairKet) : PairKet := fun a d =>
  amp (applyCorrection m (v a 0, v a 1)) d

theorem swapping_contraction_formula (m : BellMeasurement) :
    swappingContraction m swappingInput = (1 / 2 : ℂ) • bellKet m := by
  funext a d
  cases m <;> fin_cases a <;> fin_cases d <;>
    simp [swappingContraction, swappingInput, bellKet] <;>
    ring_nf <;> norm_num [bellCoeff_sq, bellCoeff_cube, bellCoeff_four]

theorem swapping_projection_formula (m : BellMeasurement) :
    swappingProject m swappingInput = (1 / 2 : ℂ) • normalizedSwap m := by
  funext a b c d
  simp only [swappingProject, swapping_contraction_formula, normalizedSwap,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem swapped_outer_eq_bell (m : BellMeasurement) : swappedOuter m = bellKet m := by
  rw [swappedOuter, swapping_contraction_formula, smul_smul]
  norm_num

theorem swapping_exact_correction (m : BellMeasurement) :
    correctOuter m (swappedOuter m) = bellKet .phiPlus := by
  rw [swapped_outer_eq_bell]
  funext a d
  cases m <;> fin_cases a <;> fin_cases d <;> simp [correctOuter, amp, applyCorrection, bellKet]

theorem swapping_canonical_decomposition :
    swappingInput = swappingProject .phiPlus swappingInput +
      swappingProject .phiMinus swappingInput + swappingProject .psiPlus swappingInput +
      swappingProject .psiMinus swappingInput := by
  simp only [swapping_projection_formula]
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [swappingInput, normalizedSwap, bellKet] <;> ring

def pairNormSq (v : PairKet) : ℝ := ∑ a, ∑ d, Complex.normSq (v a d)
def fourNormSq (v : FourKet) : ℝ := ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (v a b c d)

theorem bell_pair_normalized (m : BellMeasurement) : pairNormSq (bellKet m) = 1 := by
  cases m <;> norm_num [pairNormSq, bellKet, Fin.sum_univ_two]

theorem swapping_input_normalized : fourNormSq swappingInput = 1 := by
  norm_num [fourNormSq, swappingInput, bellKet, Fin.sum_univ_two, Complex.normSq_mul]

theorem normalized_swap_norm (m : BellMeasurement) : fourNormSq (normalizedSwap m) = 1 := by
  cases m <;> norm_num [fourNormSq, normalizedSwap, bellKet, Fin.sum_univ_two, Complex.normSq_mul]

theorem actual_normalized_projection (m : BellMeasurement) :
    (2 : ℂ) • swappingProject m swappingInput = normalizedSwap m := by
  rw [swapping_projection_formula, smul_smul]
  norm_num

def swapOutcomeProbability (m : BellMeasurement) : ℝ :=
  fourNormSq (swappingProject m swappingInput)

theorem swapping_success_probability (m : BellMeasurement) : swapOutcomeProbability m = 1 / 4 := by
  rw [swapOutcomeProbability, swapping_projection_formula]
  cases m <;> norm_num [fourNormSq, normalizedSwap, bellKet, Fin.sum_univ_two, Complex.normSq_mul]

theorem all_outcomes_success : swapOutcomeProbability .phiPlus + swapOutcomeProbability .phiMinus +
    swapOutcomeProbability .psiPlus + swapOutcomeProbability .psiMinus = 1 := by
  simp only [swapping_success_probability]
  norm_num

def pairDeterminant (v : PairKet) : ℂ := v 0 0 * v 1 1 - v 0 1 * v 1 0

theorem bell_determinant_nonzero (m : BellMeasurement) : pairDeterminant (bellKet m) ≠ 0 := by
  cases m <;> simp [pairDeterminant, bellKet, bellCoeff_ne_zero]

theorem bell_not_product (m : BellMeasurement) :
    ¬ ∃ u v : QubitState, bellKet m = fun a d => amp u a * amp v d := by
  rintro ⟨u, v, h⟩
  apply bell_determinant_nonzero m
  rw [h]
  simp only [pairDeterminant, amp]
  norm_num
  ring

theorem swapping_target_entanglement (m : BellMeasurement) :
    correctOuter m (swappedOuter m) = bellKet .phiPlus ∧
    ¬ ∃ u v : QubitState, correctOuter m (swappedOuter m) = fun a d => amp u a * amp v d := by
  rw [swapping_exact_correction]
  exact ⟨rfl, bell_not_product .phiPlus⟩

def purePairDensity (v : PairKet) : PairDensity :=
  Matrix.vecMulVec (fun i => v i.1 i.2) (star (fun i => v i.1 i.2))

theorem pure_pair_positive (v : PairKet) : (purePairDensity v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem pure_pair_trace (v : PairKet) : (purePairDensity v).trace = (pairNormSq v : ℂ) := by
  simp [purePairDensity, Matrix.trace, Matrix.diag, Matrix.vecMulVec, pairNormSq,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.mul_conj, Complex.ofReal_add]

def outerReduced (v : FourKet) : PairDensity := fun i j =>
  ∑ b, ∑ c, v i.1 b c i.2 * star (v j.1 b c j.2)

theorem swapped_outer_density (m : BellMeasurement) :
    outerReduced (normalizedSwap m) = purePairDensity (bellKet m) := by
  ext i j
  rcases i with ⟨a, d⟩
  rcases j with ⟨a', d'⟩
  cases m <;> fin_cases a <;> fin_cases d <;> fin_cases a' <;> fin_cases d' <;>
    simp [outerReduced, normalizedSwap, purePairDensity, Matrix.vecMulVec, bellKet,
      Fin.sum_univ_two, map_mul, map_neg] <;>
    ring_nf <;> norm_num [bellCoeff_sq, bellCoeff_cube, bellCoeff_four]

theorem swapped_density_trace_one (m : BellMeasurement) :
    (outerReduced (normalizedSwap m)).trace = 1 := by
  rw [swapped_outer_density, pure_pair_trace, bell_pair_normalized]
  norm_num

def rejectedFormula (F : ℚ) : ℚ :=
  (F ^ 2 + (1 - F) ^ 3 / 3) / (F ^ 2 + 2 * F * (1 - F) + (5 / 3) * (1 - F) ^ 2)

theorem rejected_formula_counterexamples : rejectedFormula 0 = 1 / 5 ∧
    rejectedFormula (3 / 4) = 109 / 200 ∧ rejectedFormula (3 / 4) < 3 / 4 := by
  norm_num [rejectedFormula]

def labelWeight (F : ℚ) (phaseError : Bool) : ℚ := if phaseError then 1 - F else F
def independentWeight (F : ℚ) (a b : Bool) : ℚ := labelWeight F a * labelWeight F b
def acceptedMass (F : ℚ) : ℚ := ∑ a : Bool, ∑ b : Bool, if a = b then independentWeight F a b else 0
def acceptedGoodMass (F : ℚ) : ℚ :=
  ∑ a : Bool, ∑ b : Bool, if a = false ∧ a = b then independentWeight F a b else 0
def acceptedBadMass (F : ℚ) : ℚ :=
  ∑ a : Bool, ∑ b : Bool, if a = true ∧ a = b then independentWeight F a b else 0

theorem joint_weights_sum (F : ℚ) : (∑ a : Bool, ∑ b : Bool, independentWeight F a b) = 1 := by
  simp [independentWeight, labelWeight]
  ring

theorem joint_weights_nonnegative (F : ℚ) (hF : 0 ≤ F ∧ F ≤ 1) (a b : Bool) :
    0 ≤ independentWeight F a b := by
  apply mul_nonneg <;> cases a <;> cases b <;>
    simp only [labelWeight, Bool.false_eq_true, ↓reduceIte] <;> linarith

theorem independent_marginal (F : ℚ) (a : Bool) :
    (∑ b : Bool, independentWeight F a b) = labelWeight F a := by
  cases a <;> simp [independentWeight, labelWeight] <;> ring

theorem accepted_mass_formula (F : ℚ) : acceptedMass F = F ^ 2 + (1 - F) ^ 2 := by
  simp [acceptedMass, independentWeight, labelWeight, pow_two, add_comm]

theorem good_mass_formula (F : ℚ) : acceptedGoodMass F = F ^ 2 := by
  simp [acceptedGoodMass, independentWeight, labelWeight, pow_two]

theorem bad_mass_formula (F : ℚ) : acceptedBadMass F = (1 - F) ^ 2 := by
  simp [acceptedBadMass, independentWeight, labelWeight, pow_two]

theorem accepted_mass_positive (F : ℚ) : 0 < acceptedMass F := by
  rw [accepted_mass_formula]
  nlinarith [sq_nonneg (F - 1 / 2)]

theorem purification_success_bounds (F : ℚ) (hF : 0 ≤ F ∧ F ≤ 1) :
    1 / 2 ≤ acceptedMass F ∧ acceptedMass F ≤ 1 := by
  rw [accepted_mass_formula]
  have h := mul_nonneg hF.1 (sub_nonneg.mpr hF.2)
  constructor <;> nlinarith [sq_nonneg (F - 1 / 2)]

/-- Posterior obtained by normalizing the actual accepted-good weight. -/
def purifiedFidelity (F : ℚ) : ℚ := acceptedGoodMass F / acceptedMass F
def purificationStep (F : ℚ) (_hF : 0 ≤ F ∧ F ≤ 1) : ℚ := purifiedFidelity F

theorem purification_posterior_formula (F : ℚ) :
    purifiedFidelity F = F ^ 2 / (F ^ 2 + (1 - F) ^ 2) := by
  rw [purifiedFidelity, good_mass_formula, accepted_mass_formula]

theorem purification_bounds_invariant (F : ℚ) :
    0 ≤ purifiedFidelity F ∧ purifiedFidelity F ≤ 1 := by
  have hp := accepted_mass_positive F
  rw [purifiedFidelity, good_mass_formula]
  exact ⟨div_nonneg (sq_nonneg _) hp.le,
    (div_le_one hp).mpr (by rw [accepted_mass_formula]; nlinarith [sq_nonneg (1 - F)])⟩

theorem purification_difference (F : ℚ) :
    purifiedFidelity F - F = F * (1 - F) * (2 * F - 1) / acceptedMass F := by
  have hp := ne_of_gt (accepted_mass_positive F)
  rw [purifiedFidelity, good_mass_formula]
  field_simp
  rw [accepted_mass_formula]
  ring

theorem purification_strict_improvement (F : ℚ) (hF : 1 / 2 < F ∧ F < 1) :
    F < purifiedFidelity F := by
  have hnum : 0 < F * (1 - F) * (2 * F - 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have h := div_pos hnum (accepted_mass_positive F)
  rw [← purification_difference] at h
  linarith

theorem purification_improvement_iff (F : ℚ) (hF : 0 ≤ F ∧ F ≤ 1) :
    F < purifiedFidelity F ↔ 1 / 2 < F ∧ F < 1 := by
  constructor
  · intro h
    have hlt : F < 1 := h.trans_le (purification_bounds_invariant F).2
    refine ⟨?_, hlt⟩
    by_contra hhalf
    have hn : F * (1 - F) * (2 * F - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hF.1 (sub_nonneg.mpr hF.2)) (by linarith)
    have hd := div_nonpos_of_nonpos_of_nonneg hn (accepted_mass_positive F).le
    rw [← purification_difference] at hd
    linarith
  · exact purification_strict_improvement F

theorem fixed_points_purification :
    purifiedFidelity 0 = 0 ∧ purifiedFidelity (1 / 2) = 1 / 2 ∧ purifiedFidelity 1 = 1 := by
  norm_num [purification_posterior_formula]

theorem purification_fixed_iff (F : ℚ) :
    purifiedFidelity F = F ↔ F = 0 ∨ F = 1 / 2 ∨ F = 1 := by
  constructor
  · intro h
    have heq := purification_difference F
    rw [h, sub_self] at heq
    have hn : F * (1 - F) * (2 * F - 1) = 0 :=
      (div_eq_zero_iff.mp heq.symm).resolve_right (ne_of_gt (accepted_mass_positive F))
    rcases mul_eq_zero.mp hn with hf | hf
    · rcases mul_eq_zero.mp hf with hf | hf
      · exact Or.inl hf
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inr (Or.inl (by linarith))
  · rintro (rfl | rfl | rfl)
    · exact fixed_points_purification.1
    · exact fixed_points_purification.2.1
    · exact fixed_points_purification.2.2

theorem purification_bad_posterior (F : ℚ) :
    acceptedBadMass F / acceptedMass F = 1 - purifiedFidelity F := by
  have hp := ne_of_gt (accepted_mass_positive F)
  rw [purifiedFidelity, good_mass_formula, bad_mass_formula]
  field_simp
  rw [accepted_mass_formula]
  ring

def phaseDensity (F : ℚ) : PairDensity :=
  (F : ℝ) • purePairDensity (bellKet .phiPlus) +
    (1 - (F : ℝ)) • purePairDensity (bellKet .phiMinus)

theorem phase_density_positive (F : ℚ) (hF : 0 ≤ F ∧ F ≤ 1) : (phaseDensity F).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact (pure_pair_positive _).smul (show (0 : ℝ) ≤ F by exact_mod_cast hF.1)
  · exact (pure_pair_positive _).smul
      (show (0 : ℝ) ≤ 1 - (F : ℝ) by exact_mod_cast sub_nonneg.mpr hF.2)

theorem phase_density_hermitian (F : ℚ) (hF : 0 ≤ F ∧ F ≤ 1) :
    (phaseDensity F).IsHermitian := (phase_density_positive F hF).isHermitian

theorem phase_density_trace (F : ℚ) : (phaseDensity F).trace = 1 := by
  simp [phaseDensity, Matrix.trace_add, Matrix.trace_smul, pure_pair_trace, bell_pair_normalized]

def targetOverlap (ρ : PairDensity) : ℂ :=
  ∑ i : PairIndex, ∑ j : PairIndex,
    star (bellKet .phiPlus i.1 i.2) * ρ i j * bellKet .phiPlus j.1 j.2

theorem phase_density_fidelity (F : ℚ) : targetOverlap (phaseDensity F) = (F : ℂ) := by
  simp [targetOverlap, phaseDensity, purePairDensity, Matrix.vecMulVec, bellKet,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.real_smul]
  ring_nf
  norm_num [bellCoeff_sq, bellCoeff_four]
  ring

def labelBell (b : Bool) : PairKet := if b then bellKet .phiMinus else bellKet .phiPlus

/-- Conditional matrix from the four independent label weights and equality acceptance. -/
def filteredDensity (F : ℚ) : PairDensity :=
  ∑ a : Bool, ∑ b : Bool, if a = b then
    ((independentWeight F a b / acceptedMass F : ℚ) : ℝ) • purePairDensity (labelBell a) else 0

theorem filtered_density_formula (F : ℚ) :
    filteredDensity F = phaseDensity (purifiedFidelity F) := by
  have hb := purification_bad_posterior F
  rw [bad_mass_formula] at hb
  simp only [filteredDensity, Fintype.sum_bool, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, independentWeight, labelWeight, labelBell, phaseDensity]
  have hg : F * F / acceptedMass F = purifiedFidelity F := by
    rw [purifiedFidelity, good_mass_formula, pow_two]
  have hb' : (1 - F) * (1 - F) / acceptedMass F = 1 - purifiedFidelity F := by
    simpa [pow_two] using hb
  rw [hg, hb']
  push_cast
  simp [add_comm]

theorem filtered_density_valid (F : ℚ) :
    (filteredDensity F).PosSemidef ∧ (filteredDensity F).trace = 1 ∧
      targetOverlap (filteredDensity F) = (purifiedFidelity F : ℂ) := by
  rw [filtered_density_formula]
  exact ⟨phase_density_positive _ (purification_bounds_invariant F),
    phase_density_trace _, phase_density_fidelity _⟩

structure QuantumEntanglementSwappingPurificationSuite : Prop where
  contraction : ∀ (m : BellMeasurement),
    swappingContraction m swappingInput = (1 / 2 : ℂ) • bellKet m
  projection : ∀ (m : BellMeasurement),
    swappingProject m swappingInput = (1 / 2 : ℂ) • normalizedSwap m
  normalized_branch : ∀ (m : BellMeasurement), fourNormSq (normalizedSwap m) = 1
  probability : ∀ (m : BellMeasurement), swapOutcomeProbability m = 1 / 4
  correction : ∀ (m : BellMeasurement), correctOuter m (swappedOuter m) = bellKet .phiPlus
  entangled : ∀ (m : BellMeasurement),
    ¬ ∃ u v : QubitState, correctOuter m (swappedOuter m) = fun a d => amp u a * amp v d
  outer_density : ∀ (m : BellMeasurement),
    outerReduced (normalizedSwap m) = purePairDensity (bellKet m)
  outer_trace : ∀ (m : BellMeasurement), (outerReduced (normalizedSwap m)).trace = 1
  valid_weights : ∀ (F : ℚ), 0 ≤ F ∧ F ≤ 1 → ∀ a b, 0 ≤ independentWeight F a b
  weight_sum : ∀ (F : ℚ), (∑ a : Bool, ∑ b : Bool, independentWeight F a b) = 1
  success : ∀ (F : ℚ), 0 ≤ F ∧ F ≤ 1 → 1 / 2 ≤ acceptedMass F ∧ acceptedMass F ≤ 1
  posterior : ∀ (F : ℚ), purifiedFidelity F = F ^ 2 / (F ^ 2 + (1 - F) ^ 2)
  bounds : ∀ (F : ℚ), 0 ≤ purifiedFidelity F ∧ purifiedFidelity F ≤ 1
  improvement : ∀ (F : ℚ), 1 / 2 < F ∧ F < 1 → F < purifiedFidelity F
  fixed : ∀ (F : ℚ), purifiedFidelity F = F ↔ F = 0 ∨ F = 1 / 2 ∨ F = 1
  density_positive : ∀ (F : ℚ), 0 ≤ F ∧ F ≤ 1 → (phaseDensity F).PosSemidef
  density_trace : ∀ (F : ℚ), (phaseDensity F).trace = 1
  density_fidelity : ∀ (F : ℚ), targetOverlap (phaseDensity F) = (F : ℂ)
  filtered_formula : ∀ (F : ℚ), filteredDensity F = phaseDensity (purifiedFidelity F)
  filtered_valid : ∀ (F : ℚ), (filteredDensity F).PosSemidef ∧
    (filteredDensity F).trace = 1 ∧
    targetOverlap (filteredDensity F) = (purifiedFidelity F : ℂ)

theorem verification_suite : QuantumEntanglementSwappingPurificationSuite := {
  contraction := swapping_contraction_formula
  projection := swapping_projection_formula
  normalized_branch := normalized_swap_norm
  probability := swapping_success_probability
  correction := swapping_exact_correction
  entangled := fun m => (swapping_target_entanglement m).2
  outer_density := swapped_outer_density
  outer_trace := swapped_density_trace_one
  valid_weights := joint_weights_nonnegative
  weight_sum := joint_weights_sum
  success := purification_success_bounds
  posterior := purification_posterior_formula
  bounds := purification_bounds_invariant
  improvement := purification_strict_improvement
  fixed := purification_fixed_iff
  density_positive := phase_density_positive
  density_trace := phase_density_trace
  density_fidelity := phase_density_fidelity
  filtered_formula := filtered_density_formula
  filtered_valid := filtered_density_valid
}

end
end QuantumEntanglementSwappingPurificationContract

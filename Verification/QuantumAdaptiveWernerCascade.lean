/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumWernerCascade

/-! Adaptive Werner swapping with faithful classical delivery and detector loss. -/
noncomputable section
namespace QuantumAdaptiveWernerCascade
open QuantumWernerCascade QuantumCascadedSwapping QuantumCascadeReduction
open QuantumCentralDepolarization QuantumNoisyVisibility QuantumGateNoiseComposition
open QuantumStateAvailabilityContract QuantumGeneralBellReadout QuantumOutcomeInstrument
open QuantumBellDiagonalInputs QuantumBellDiagonalSwapping QuantumRectangularSwapping
open QuantumSwappingInstrument QuantumMixedEnvironment QuantumPauliDensityBridge
open QuantumEntanglementSwappingPurificationContract QuantumNoisyBellInstrument
open scoped BigOperators ComplexOrder Matrix Kronecker

variable {e : Type} [Fintype e] [DecidableEq e]

def lossyFaithfulReadout (η : BellMeasurement → ℝ)
    (lo : ∀ m, 0 ≤ η m) (hi : ∀ m, η m ≤ 1) : Readout where
  detection := η
  detection_nonneg := lo
  detection_le_one := hi
  confusion := fun m r => if m = r then 1 else 0
  confusion_nonneg := by intro m r; split_ifs <;> norm_num
  confusion_sum := by intro m; simp

def wernerRoundWithReadout (b c : Visibility) (model : Readout) :
    Round e (Option (PairIndex × PairIndex)) :=
  preRound (centralChannel (depolarizing b)) (fun _ => depolarizing c) model

/-- Individual corrected sandwich, before any aggregation over measurement outcomes. -/
theorem faithful_sandwich (p q : BellDistribution) (r : BellMeasurement) :
    branchOperator r r * inputDensity p q * (branchOperator r r).conjTranspose =
      (1 / 4 : ℝ) • idealDensity p q := by
  simp only [inputDensity, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, component_refinement, xor_cancel, idealDensity, Finset.smul_sum,
    smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

theorem faithful_mixed_sandwich (r : BellMeasurement) :
    branchOperator r r * fullyMixedFour * (branchOperator r r).conjTranspose =
      (1 / 4 : ℝ) • maximallyMixed := by
  rw [fully_mixed_input, faithful_sandwich, uniform_input_erases_ideal_output]

theorem lossy_reported (η : BellMeasurement → ℝ) (lo hi)
    {κ ι : Type} [Fintype κ] [Fintype ι]
    (pre : CPTP FourIndex κ) (post : CPTP PairIndex ι) (r : BellMeasurement) (M : FourDensity) :
    noisyReported pre (fun _ => post) (lossyFaithfulReadout η lo hi) r M =
      post.map ((η r : ℂ) •
        (branchOperator r r * pre.map M * (branchOperator r r).conjTranspose)) := by
  simp only [noisyReported, noisyMicro, microMap, weight, lossyFaithfulReadout,
    mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  simp [apply_ite, CPTP.map, Complex.coe_smul]

theorem ideal_isotropic (w v : Visibility) :
    idealDensity (isotropicDistribution w.val ⟨w.nonnegative, w.le_one⟩)
      (isotropicDistribution v.val ⟨v.nonnegative, v.le_one⟩) =
      isotropic (multiplyVisibility w v) :=
  isotropic_visibility_product _ _ _ _

theorem wernerRound_lossy_single_branch_map (b c w v : Visibility)
    (η : BellMeasurement → ℝ) (lo hi) (σ : EnvironmentState e) (r : BellMeasurement) :
    ((wernerRoundWithReadout b c (lossyFaithfulReadout η lo hi)).branch (some r)).map
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ.matrix) =
      ((η r / 4 : ℝ) : ℂ) •
        isotropic (multiplyVisibility c (multiplyVisibility b (multiplyVisibility w v))) := by
  rw [wernerRoundWithReadout, preRound_map, trace_tensor_state]
  change noisyReported _ _ _ r _ = _
  rw [lossy_reported]
  have ht : isotropic w ⊗ₖ isotropic v =
      inputDensity (isotropicDistribution w.val ⟨w.nonnegative, w.le_one⟩)
        (isotropicDistribution v.val ⟨v.nonnegative, v.le_one⟩) :=
    (input_density_tensor _ _).symm
  rw [ht, central_input_depolarization]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    faithful_sandwich, faithful_mixed_sandwich, Complex.coe_smul]
  rw [ideal_isotropic]
  have hm (g x : Visibility) : g.val • isotropic x +
      (1 - g.val) • maximallyMixed = isotropic (multiplyVisibility g x) := by
    simpa only [Complex.coe_smul] using isotropic_mix g x
  rw [smul_comm b.val, smul_comm (1 - b.val), ← smul_add, hm, smul_smul]
  rw [show ∀ (a : ℝ) M, (depolarizing c).map (a • M) =
      a • (depolarizing c).map M from
    fun a M => ((depolarizing c).linear.restrictScalars ℝ).map_smul a M]
  rw [depolarizing_isotropic]
  congr 1
  ring


/-- Bounded detector efficiencies, with exact delivery of every detected label. -/
structure Efficiency where
  val : BellMeasurement → ℝ
  nonnegative : ∀ r, 0 ≤ val r
  le_one : ∀ r, val r ≤ 1

def Efficiency.readout (η : Efficiency) : Readout :=
  lossyFaithfulReadout η.val η.nonnegative η.le_one

structure Schedule where
  bsm : BellMeasurement → Visibility
  corr : BellMeasurement → Visibility
  fresh : BellMeasurement → Visibility

def Schedule.alpha (s : Schedule) (r : BellMeasurement) : Visibility :=
  multiplyVisibility (s.corr r) (multiplyVisibility (s.bsm r) (s.fresh r))

def adaptiveCascade {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b c : Visibility) (s : Schedule)
    (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (σ₂ : BellMeasurement → EnvironmentState e₂) :
    Cascade e₁ e₂ (Option (PairIndex × PairIndex)) (Option (PairIndex × PairIndex)) where
  first := wernerRoundWithReadout b c η₁.readout
  second := fun r => wernerRoundWithReadout (s.bsm r) (s.corr r) (η₂ r).readout
  freshPair := fun r => pairResource (s.fresh r)
  freshMemory := σ₂

def outputVisibility (b c w v : Visibility) (s : Schedule) (r : BellMeasurement) :
    Visibility := multiplyVisibility (s.corr r) (multiplyVisibility (s.bsm r)
      (multiplyVisibility (multiplyVisibility c
        (multiplyVisibility b (multiplyVisibility w v))) (s.fresh r)))

theorem adaptive_branch_matrix {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b c w v : Visibility) (s : Schedule)
    (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (σ₁ : EnvironmentState e₁) (σ₂ : BellMeasurement → EnvironmentState e₂)
    (r t : BellMeasurement) :
    (cascadeBranch (adaptiveCascade b c s η₁ η₂ σ₂) r (some t)).map
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix) =
      ((η₁.val r * (η₂ r).val t / 16 : ℝ) : ℂ) •
        isotropic (outputVisibility b c w v s r) := by
  rw [cascadeBranch, KrausBranch.comp_map]
  change (continuation _ r (some t)).map
    (((wernerRoundWithReadout b c η₁.readout).branch (some r)).map _) = _
  simp only [Efficiency.readout]
  rw [wernerRound_lossy_single_branch_map b c w v η₁.val
    η₁.nonnegative η₁.le_one σ₁ r]
  rw [show ∀ (K : KrausBranch PairIndex PairIndex) (a : ℂ) M,
    K.map (a • M) = a • K.map M from fun K a M => K.linear.map_smul a M]
  simp only [continuation, KrausBranch.comp_map, preparation_map]
  change ((η₁.val r / 4 : ℝ) : ℂ) •
    (((wernerRoundWithReadout (s.bsm r) (s.corr r) (η₂ r).readout).branch (some t)).map
      ((isotropic _ ⊗ₖ isotropic (s.fresh r)) ⊗ₖ (σ₂ r).matrix)) = _
  simp only [Efficiency.readout]
  rw [wernerRound_lossy_single_branch_map (s.bsm r) (s.corr r) _ (s.fresh r)
    (η₂ r).val (η₂ r).nonnegative (η₂ r).le_one (σ₂ r) t, smul_smul]
  congr 1
  push_cast
  ring

def branchSuccessWeight (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (r : BellMeasurement) : ℝ := (η₁.val r / 16) * ∑ t, (η₂ r).val t

def totalSuccessProb (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency) : ℝ :=
  ∑ r, branchSuccessWeight η₁ η₂ r

theorem branch_weight_nonnegative (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (r : BellMeasurement) : 0 ≤ branchSuccessWeight η₁ η₂ r :=
  mul_nonneg (div_nonneg (η₁.nonnegative r) (by norm_num))
    (Finset.sum_nonneg fun t _ => (η₂ r).nonnegative t)

theorem adaptive_success_matrix {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b c w v : Visibility) (s : Schedule)
    (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (σ₁ : EnvironmentState e₁) (σ₂ : BellMeasurement → EnvironmentState e₂) :
    acceptedCascade (adaptiveCascade b c s η₁ η₂ σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix) =
      ∑ r, (branchSuccessWeight η₁ η₂ r : ℂ) •
        isotropic (outputVisibility b c w v s r) := by
  simp only [acceptedCascade, adaptive_branch_matrix, ← Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  simp only [branchSuccessWeight, Finset.mul_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro t _
  push_cast
  ring

theorem adaptive_success_trace {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b c w v : Visibility) (s : Schedule)
    (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (σ₁ : EnvironmentState e₁) (σ₂ : BellMeasurement → EnvironmentState e₂) :
    (acceptedCascade (adaptiveCascade b c s η₁ η₂ σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix)).trace =
      (totalSuccessProb η₁ η₂ : ℂ) := by
  simp [adaptive_success_matrix, Matrix.trace_sum, Matrix.trace_smul,
    isotropic_trace, totalSuccessProb]



/-- Algebraic affine extension; physical inputs use bounded Visibility. -/
def wernerMatrix (x : ℝ) : PairDensity :=
  x • isotropic ⟨1, by norm_num, le_rfl⟩ + (1 - x) • maximallyMixed

theorem isotropic_affine (x : Visibility) : isotropic x = wernerMatrix x.val := by
  have h : multiplyVisibility x ⟨1, by norm_num, le_rfl⟩ = x := by
    cases x
    simp [multiplyVisibility]
  simpa only [h, Complex.coe_smul, wernerMatrix] using
    (isotropic_mix x ⟨1, by norm_num, le_rfl⟩).symm

theorem affine_weighted_sum (q x : BellMeasurement → ℝ) :
    (∑ r, q r • wernerMatrix (x r)) =
      (∑ r, q r * x r) • isotropic ⟨1, by norm_num, le_rfl⟩ +
        ((∑ r, q r) - ∑ r, q r * x r) • maximallyMixed := by
  simp only [wernerMatrix, smul_add, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul, mul_sub, mul_one, Finset.sum_sub_distrib]

theorem affine_conditional (q x : BellMeasurement → ℝ) (hp : 0 < ∑ r, q r) :
    (∑ r, q r)⁻¹ • (∑ r, q r • wernerMatrix (x r)) =
      wernerMatrix ((∑ r, q r * x r) / ∑ r, q r) := by
  rw [affine_weighted_sum, wernerMatrix, smul_add, smul_smul, smul_smul]
  congr 1
  · ring
  · field_simp

theorem zero_weight_sum (q : BellMeasurement → ℝ) (hq : ∀ r, 0 ≤ q r)
    (hz : ∑ r, q r = 0) : ∀ r, q r = 0 := by
  exact fun r => (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hq t)).mp hz r
    (Finset.mem_univ r)

def weightedAlpha (s : Schedule) (η₁ : Efficiency)
    (η₂ : BellMeasurement → Efficiency) : ℝ :=
  (∑ r, branchSuccessWeight η₁ η₂ r * (s.alpha r).val) / totalSuccessProb η₁ η₂

theorem positive_branch_total (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (r : BellMeasurement) (hr : 0 < branchSuccessWeight η₁ η₂ r) :
    0 < totalSuccessProb η₁ η₂ := by
  exact hr.trans_le (Finset.single_le_sum
    (fun t _ => branch_weight_nonnegative η₁ η₂ t) (Finset.mem_univ r))

theorem weightedAlpha_bounds (s : Schedule) (η₁ : Efficiency)
    (η₂ : BellMeasurement → Efficiency) (hp : 0 < totalSuccessProb η₁ η₂) :
    0 ≤ weightedAlpha s η₁ η₂ ∧ weightedAlpha s η₁ η₂ ≤ 1 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun r _ =>
      mul_nonneg (branch_weight_nonnegative η₁ η₂ r) (s.alpha r).nonnegative) hp.le
  · apply (div_le_one hp).mpr
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_of_le_one_right (branch_weight_nonnegative η₁ η₂ r) (s.alpha r).le_one

theorem heralded_branch_comparison_weighted (s : Schedule) (η₁ : Efficiency)
    (η₂ : BellMeasurement → Efficiency) (r : BellMeasurement) (w : ℝ)
    (hq : 0 < branchSuccessWeight η₁ η₂ r) (hw : 0 < w)
    (ha : weightedAlpha s η₁ η₂ < (s.alpha r).val) :
    0 < totalSuccessProb η₁ η₂ ∧
    wernerFidelity (weightedAlpha s η₁ η₂ * w) <
      wernerFidelity ((s.alpha r).val * w) ∧
    wernerFidelity ((s.alpha r).val * w) ≤ wernerFidelity w := by
  refine ⟨positive_branch_total η₁ η₂ r hq, ?_, ?_⟩
  · unfold wernerFidelity
    nlinarith [mul_lt_mul_of_pos_right ha hw]
  · unfold wernerFidelity
    nlinarith [mul_le_of_le_one_left hw.le (s.alpha r).le_one]



theorem output_visibility_value (b c w v : Visibility) (s : Schedule) (r : BellMeasurement) :
    (outputVisibility b c w v s r).val = (s.alpha r).val * (c.val * b.val * w.val * v.val) := by
  simp only [outputVisibility, Schedule.alpha, multiplyVisibility]
  ring

section OperatorConditioning
variable {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
  [Fintype e₂] [DecidableEq e₂]
variable (b c w v : Visibility) (s : Schedule)
  (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
  (σ₁ : EnvironmentState e₁) (σ₂ : BellMeasurement → EnvironmentState e₂)

theorem adaptive_success_zero (hp : totalSuccessProb η₁ η₂ = 0) :
    acceptedCascade (adaptiveCascade b c s η₁ η₂ σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix) = 0 := by
  rw [adaptive_success_matrix]
  have hz := zero_weight_sum _ (branch_weight_nonnegative η₁ η₂) hp
  simp only [hz, Complex.ofReal_zero, zero_smul, Finset.sum_const_zero]

theorem adaptive_success_conditional (hp : 0 < totalSuccessProb η₁ η₂) :
    (totalSuccessProb η₁ η₂ : ℂ)⁻¹ •
      acceptedCascade (adaptiveCascade b c s η₁ η₂ σ₂)
        ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix) =
      wernerMatrix (weightedAlpha s η₁ η₂ * (c.val * b.val * w.val * v.val)) := by
  rw [adaptive_success_matrix]
  simp only [isotropic_affine, ← Complex.ofReal_inv, Complex.coe_smul]
  unfold totalSuccessProb at hp ⊢
  rw [affine_conditional _ _ hp]
  congr 1
  simp only [output_visibility_value, weightedAlpha, totalSuccessProb,
    ← mul_assoc, ← Finset.sum_mul]
  ring

theorem conditional_visibility_bounds (hp : 0 < totalSuccessProb η₁ η₂) :
    0 ≤ weightedAlpha s η₁ η₂ * (c.val * b.val * w.val * v.val) ∧
    weightedAlpha s η₁ η₂ * (c.val * b.val * w.val * v.val) ≤ 1 := by
  have ha := weightedAlpha_bounds s η₁ η₂ hp
  let hb := (multiplyVisibility c (multiplyVisibility b (multiplyVisibility w v)))
  have he : hb.val = c.val * b.val * w.val * v.val := by
    simp only [hb, multiplyVisibility]
    ring
  rw [← he]
  exact ⟨mul_nonneg ha.1 hb.nonnegative,
    (mul_le_mul_of_nonneg_right ha.2 hb.nonnegative).trans (by simpa using hb.le_one)⟩
end OperatorConditioning

def perfectEfficiency : Efficiency := ⟨fun _ => 1, fun _ => by norm_num, fun _ => le_rfl⟩
def closedEfficiency : Efficiency := ⟨fun _ => 0, fun _ => le_rfl, fun _ => by norm_num⟩

theorem perfect_branch_weight (r : BellMeasurement) :
    branchSuccessWeight perfectEfficiency (fun _ => perfectEfficiency) r = 1 / 4 := by
  unfold branchSuccessWeight
  rw [sum_bell]
  norm_num [perfectEfficiency]

theorem perfect_total_probability :
    totalSuccessProb perfectEfficiency (fun _ => perfectEfficiency) = 1 := by
  simp only [totalSuccessProb, perfect_branch_weight, sum_bell]
  norm_num

def meanAlpha (s : Schedule) : ℝ := (∑ r, (s.alpha r).val) / 4

theorem perfect_weighted_mean (s : Schedule) :
    weightedAlpha s perfectEfficiency (fun _ => perfectEfficiency) = meanAlpha s := by
  simp only [weightedAlpha, perfect_total_probability, perfect_branch_weight, div_one,
    ← Finset.mul_sum, meanAlpha]
  ring

theorem closed_first_probability (η₂ : BellMeasurement → Efficiency) :
    totalSuccessProb closedEfficiency η₂ = 0 := by
  simp [totalSuccessProb, branchSuccessWeight, closedEfficiency]

theorem closed_second_probability (η₁ : Efficiency) :
    totalSuccessProb η₁ (fun _ => closedEfficiency) = 0 := by
  simp [totalSuccessProb, branchSuccessWeight, closedEfficiency]



theorem wernerMatrix_fidelity (x : ℝ) :
    (targetOverlap (wernerMatrix x)).re = wernerFidelity x := by
  simp [wernerMatrix, targetOverlap_add, targetOverlap_real_smul, maximallyMixed_overlap,
    isotropic, density_overlap, isotropicDistribution, wernerFidelity]
  ring

theorem adaptive_selected_matrix {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b c w v : Visibility) (s : Schedule)
    (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (σ₁ : EnvironmentState e₁) (σ₂ : BellMeasurement → EnvironmentState e₂)
    (r : BellMeasurement) :
    (∑ t, (cascadeBranch (adaptiveCascade b c s η₁ η₂ σ₂) r (some t)).map
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix)) =
      (branchSuccessWeight η₁ η₂ r : ℂ) • isotropic (outputVisibility b c w v s r) := by
  simp only [adaptive_branch_matrix, ← Finset.sum_smul]
  congr 1
  simp only [branchSuccessWeight, Finset.mul_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro t _
  push_cast
  ring

theorem adaptive_selected_conditional {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (b c w v : Visibility) (s : Schedule)
    (η₁ : Efficiency) (η₂ : BellMeasurement → Efficiency)
    (σ₁ : EnvironmentState e₁) (σ₂ : BellMeasurement → EnvironmentState e₂)
    (r : BellMeasurement) (hq : 0 < branchSuccessWeight η₁ η₂ r) :
    (branchSuccessWeight η₁ η₂ r : ℂ)⁻¹ •
      (∑ t, (cascadeBranch (adaptiveCascade b c s η₁ η₂ σ₂) r (some t)).map
        ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix)) =
      wernerMatrix ((s.alpha r).val * (c.val * b.val * w.val * v.val)) := by
  rw [adaptive_selected_matrix, smul_smul, inv_mul_cancel₀
    (Complex.ofReal_ne_zero.mpr hq.ne'), one_smul, isotropic_affine, output_visibility_value]

structure QuantumAdaptiveWernerCascadeSuite : Prop where
  individual : ∀ (b c w v : Visibility) (η : Efficiency)
    (σ : EnvironmentState (Fin 2)) (r : BellMeasurement),
    ((wernerRoundWithReadout b c η.readout).branch (some r)).map
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ.matrix) =
      ((η.val r / 4 : ℝ) : ℂ) •
        isotropic (multiplyVisibility c (multiplyVisibility b (multiplyVisibility w v)))
  trace : ∀ (b c w v : Visibility) (s : Schedule) (η₁ : Efficiency)
    (η₂ : BellMeasurement → Efficiency) (σ₁ : EnvironmentState (Fin 2))
    (σ₂ : BellMeasurement → EnvironmentState (Fin 3)),
    (acceptedCascade (adaptiveCascade b c s η₁ η₂ σ₂)
      ((isotropic w ⊗ₖ isotropic v) ⊗ₖ σ₁.matrix)).trace =
      (totalSuccessProb η₁ η₂ : ℂ)

theorem verification_suite : QuantumAdaptiveWernerCascadeSuite :=
  ⟨fun b c w v η σ r => wernerRound_lossy_single_branch_map b c w v
    η.val η.nonnegative η.le_one σ r, adaptive_success_trace⟩

end QuantumAdaptiveWernerCascade

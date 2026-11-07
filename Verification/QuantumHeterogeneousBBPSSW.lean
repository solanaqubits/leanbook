/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBBPSSWConvergence
import Verification.QuantumWernerCascade

/-! Unequal independent Werner resources and a swap-then-purify operator bridge.
Polynomial identities are unconditional; normalization requires nonzero weight. -/
noncomputable section
namespace QuantumHeterogeneousBBPSSW
open QuantumCliffordTwirl QuantumBBPSSWDistillation QuantumBBPSSWConvergence
open QuantumEntanglementSwappingPurificationContract QuantumBellDiagonalInputs
open QuantumStateAvailabilityContract QuantumNoisyBellInstrument QuantumNoisySwapping
open QuantumBellDiagonalSwapping QuantumPauliDensityBridge QuantumWernerCascade
open QuantumNoisyVisibility QuantumCentralDepolarization QuantumMixedEnvironment
open Filter Topology
open scoped BigOperators ComplexOrder Matrix Kronecker

def heteroTargetMass (x y : ℝ) : ℝ := x*y + (1-x)*(1-y)/9

def heteroSuccessProb (x y : ℝ) : ℝ :=
  x*y + (x*(1-y)+(1-x)*y)/3 + 5*(1-x)*(1-y)/9

def heteroRecurrence (x y : ℝ) : ℝ := heteroTargetMass x y / heteroSuccessProb x y

def thresholdFor (x : ℝ) : ℝ := (6*x-2*x^2-1)/(-8*x^2+12*x-1)

theorem heteroSuccessProb_symm (x y : ℝ) : heteroSuccessProb x y = heteroSuccessProb y x := by
  unfold heteroSuccessProb; ring

theorem heteroRecurrence_symm (x y : ℝ) : heteroRecurrence x y = heteroRecurrence y x := by
  unfold heteroRecurrence
  rw [heteroSuccessProb_symm]
  congr 1
  unfold heteroTargetMass; ring

theorem heteroSuccessProb_diag (F : ℝ) : heteroSuccessProb F F = successProbability F := by
  unfold heteroSuccessProb successProbability; ring

theorem heteroRecurrence_diag (F : ℝ) : heteroRecurrence F F = recurrence F := by
  unfold heteroRecurrence recurrence
  rw [heteroSuccessProb_diag]
  congr 1
  unfold heteroTargetMass QuantumBBPSSWDistillation.targetMass; ring

/-- The four candidate Bell weights; their circuit refinement is proved below. -/
def acceptedBellMatrix (x y : ℝ) : PairDensity :=
  heteroTargetMass x y • bellProjector .phiPlus +
    (x*((1-y)/3)+((1-x)/3)*y) • bellProjector .phiMinus +
    (2*((1-x)/3)*((1-y)/3)) • (bellProjector .psiPlus + bellProjector .psiMinus)

theorem accepted_hetero_row00 (x y : ℝ) (j : PairIndex) :
    accepted.map (werner x ⊗ₖ werner y) (0,0) j = acceptedBellMatrix x y (0,0) j := by
  rw [accepted_entry]
  rcases j with ⟨c,d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [Fin.sum_univ_two, Fin.add_def, QuantumBBPSSWDistillation.flip,
      Matrix.kroneckerMap_apply, werner, heteroTargetMass, acceptedBellMatrix,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      bellProjector, purePairDensity, Matrix.vecMulVec, bellKet] <;>
    ring_nf <;> norm_num [bellCoeff_sq, bellCoeff_four] <;> ring

theorem accepted_hetero_row01 (x y : ℝ) (j : PairIndex) :
    accepted.map (werner x ⊗ₖ werner y) (0,1) j = acceptedBellMatrix x y (0,1) j := by
  rw [accepted_entry]
  rcases j with ⟨c,d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [Fin.sum_univ_two, Fin.add_def, QuantumBBPSSWDistillation.flip,
      Matrix.kroneckerMap_apply, werner, heteroTargetMass, acceptedBellMatrix,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      bellProjector, purePairDensity, Matrix.vecMulVec, bellKet]
  ring_nf
  norm_num [bellCoeff_sq, bellCoeff_four]
  ring

theorem accepted_hetero_row10 (x y : ℝ) (j : PairIndex) :
    accepted.map (werner x ⊗ₖ werner y) (1,0) j = acceptedBellMatrix x y (1,0) j := by
  rw [accepted_entry]
  rcases j with ⟨c,d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [Fin.sum_univ_two, Fin.add_def, QuantumBBPSSWDistillation.flip,
      Matrix.kroneckerMap_apply, werner, heteroTargetMass, acceptedBellMatrix,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      bellProjector, purePairDensity, Matrix.vecMulVec, bellKet]
  ring_nf
  norm_num [bellCoeff_sq, bellCoeff_four]
  ring

theorem accepted_hetero_row11 (x y : ℝ) (j : PairIndex) :
    accepted.map (werner x ⊗ₖ werner y) (1,1) j = acceptedBellMatrix x y (1,1) j := by
  rw [accepted_entry]
  rcases j with ⟨c,d⟩
  fin_cases c <;> fin_cases d <;>
    norm_num [Fin.sum_univ_two, Fin.add_def, QuantumBBPSSWDistillation.flip,
      Matrix.kroneckerMap_apply, werner, heteroTargetMass, acceptedBellMatrix,
      Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      bellProjector, purePairDensity, Matrix.vecMulVec, bellKet] <;>
    ring_nf <;> norm_num [bellCoeff_sq, bellCoeff_four] <;> ring

/-- Direct calculation of the accepted Bell weights, before the twirl. -/
theorem accepted_hetero_matrix (x y : ℝ) :
    accepted.map (werner x ⊗ₖ werner y) = acceptedBellMatrix x y := by
  ext i j : 2
  rcases i with ⟨a,b⟩
  fin_cases a <;> fin_cases b
  · exact accepted_hetero_row00 x y j
  · exact accepted_hetero_row01 x y j
  · exact accepted_hetero_row10 x y j
  · exact accepted_hetero_row11 x y j

theorem accepted_hetero_trace (x y : ℝ) :
    (accepted.map (werner x ⊗ₖ werner y)).trace = (heteroSuccessProb x y : ℂ) := by
  rw [accepted_hetero_matrix, acceptedBellMatrix]
  simp only [Matrix.trace_add, Matrix.trace_smul, bell_projector_trace]
  simp [Complex.real_smul, heteroSuccessProb, heteroTargetMass]
  ring

theorem accepted_hetero_target (x y : ℝ) :
    targetOverlap (accepted.map (werner x ⊗ₖ werner y)) = (heteroTargetMass x y : ℂ) := by
  rw [accepted_hetero_matrix, acceptedBellMatrix]
  simp [targetOverlap_add, targetOverlap_real_smul, projector_overlap]

theorem purified_hetero_isotropic (x y : ℝ) :
    purified (werner x ⊗ₖ werner y) =
      (heteroTargetMass x y : ℂ) • bellProjector .phiPlus +
      ((heteroSuccessProb x y - heteroTargetMass x y : ℝ) / 3 : ℂ) •
        (1 - bellProjector .phiPlus) := by
  rw [purified, twirl_isotropic_formula, accepted_hetero_trace, accepted_hetero_target]
  simp only [Complex.ofReal_sub]

theorem purified_hetero_werner {x y : ℝ} (hP : heteroSuccessProb x y ≠ 0) :
    purified (werner x ⊗ₖ werner y) =
      (heteroSuccessProb x y : ℂ) • werner (heteroRecurrence x y) := by
  rw [purified, twirl_formula, accepted_hetero_trace, accepted_hetero_target]
  have hr : heteroSuccessProb x y * heteroRecurrence x y = heteroTargetMass x y := by
    unfold heteroRecurrence; exact mul_div_cancel₀ _ hP
  have hs : heteroSuccessProb x y * ((1-heteroRecurrence x y)/3) =
      (heteroSuccessProb x y-heteroTargetMass x y)/3 := by
    rw [← mul_div_assoc, mul_sub, mul_one, hr]
  simp only [werner, ← Complex.coe_smul, smul_add, smul_smul,
    ← Complex.ofReal_mul, hr, hs]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_ofNat]

theorem heteroSuccessProb_bounds {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    1 / 3 ≤ heteroSuccessProb x y ∧ heteroSuccessProb x y ≤ 1 := by
  have h00 := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)
  have h11 := mul_nonneg hx.1 hy.1
  have h10 := mul_nonneg hx.1 (sub_nonneg.mpr hy.2)
  have h01 := mul_nonneg (sub_nonneg.mpr hx.2) hy.1
  unfold heteroSuccessProb
  constructor <;> nlinarith

theorem heteroSuccessProb_pos {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 < heteroSuccessProb x y := lt_of_lt_of_le (by norm_num) (heteroSuccessProb_bounds hx hy).1

theorem heteroRecurrence_bounds {x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 ≤ heteroRecurrence x y ∧ heteroRecurrence x y ≤ 1 := by
  have hp := heteroSuccessProb_pos hx hy
  have h00 := mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hy.2)
  have h11 := mul_nonneg hx.1 hy.1
  have h10 := mul_nonneg hx.1 (sub_nonneg.mpr hy.2)
  have h01 := mul_nonneg (sub_nonneg.mpr hx.2) hy.1
  constructor
  · exact div_nonneg (by unfold heteroTargetMass; positivity) hp.le
  · apply (div_le_one hp).mpr
    unfold heteroTargetMass heteroSuccessProb
    nlinarith

theorem purified_hetero_conditional {x y : ℝ} (hP : heteroSuccessProb x y ≠ 0) :
    (heteroSuccessProb x y : ℂ)⁻¹ • purified (werner x ⊗ₖ werner y) =
      werner (heteroRecurrence x y) := by
  rw [purified_hetero_werner hP, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hP), one_smul]

theorem purified_hetero_conditional_density {x y : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    let M := (heteroSuccessProb x y : ℂ)⁻¹ • purified (werner x ⊗ₖ werner y)
    M.PosSemidef ∧ M.trace = 1 := by
  dsimp
  rw [purified_hetero_conditional (heteroSuccessProb_pos hx hy).ne']
  exact ⟨werner_positive _ (heteroRecurrence_bounds hx hy), werner_trace _⟩

theorem heteroRecurrence_sub_left {x y : ℝ} (hP : heteroSuccessProb x y ≠ 0) :
    heteroRecurrence x y - x =
      ((-8*x^2+12*x-1)*y+2*x^2-6*x+1)/(9*heteroSuccessProb x y) := by
  unfold heteroRecurrence heteroTargetMass
  field_simp [hP]
  unfold heteroSuccessProb
  ring

theorem threshold_denom_pos {x : ℝ} (h0 : 1 / 4 ≤ x) (h1 : x ≤ 1) :
    0 < -8*x^2+12*x-1 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h0) (sub_nonneg.mpr h1)]

theorem hetero_strict_improve_left_iff {x y : ℝ}
    (hx0 : 1 / 4 < x) (hx1 : x < 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    x < heteroRecurrence x y ↔ thresholdFor x < y := by
  have hp := heteroSuccessProb_pos ⟨by linarith, hx1.le⟩ hy
  have hd := threshold_denom_pos hx0.le hx1.le
  rw [← sub_pos, heteroRecurrence_sub_left hp.ne',
    div_pos_iff_of_pos_right (mul_pos (by norm_num : (0:ℝ)<9) hp)]
  unfold thresholdFor
  rw [div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

theorem hetero_strict_improve_max_iff {x y : ℝ}
    (hx : 1 / 4 < x ∧ x < 1) (hy : 1 / 4 < y ∧ y < 1) :
    max x y < heteroRecurrence x y ↔ thresholdFor x < y ∧ thresholdFor y < x := by
  rw [max_lt_iff, hetero_strict_improve_left_iff hx.1 hx.2 ⟨by linarith [hy.1],hy.2.le⟩]
  rw [heteroRecurrence_symm,
    hetero_strict_improve_left_iff hy.1 hy.2 ⟨by linarith [hx.1],hx.2.le⟩]

theorem threshold_sub_self {x : ℝ} (h : -8 * x ^ 2 + 12 * x - 1 ≠ 0) :
    thresholdFor x - x = (1-x)*(4*x-1)*(1-2*x)/(-8*x^2+12*x-1) := by
  unfold thresholdFor
  rw [div_sub' h]
  congr 1
  ring

theorem hetero_counterexample_three_quarters_three_fifths :
    heteroRecurrence (3/4) (3/5) = 83/118 ∧ heteroRecurrence (3/4) (3/5) < 3/4 := by
  norm_num [heteroRecurrence, heteroTargetMass, heteroSuccessProb]

/-- A zero trace outside the physical square does not imply a zero matrix. -/
theorem nonphysical_zero_weight_nonzero_output :
    heteroSuccessProb 1 (-1/2) = 0 ∧
    purified (werner 1 ⊗ₖ werner (-1/2)) ≠ 0 := by
  constructor
  · norm_num [heteroSuccessProb]
  · intro h
    have ht := congrArg targetOverlap h
    rw [purified, twirl_overlap, accepted_hetero_target] at ht
    norm_num [heteroTargetMass, targetOverlap] at ht

def elemFidelity (w : ℝ) : ℝ := (1+3*w)/4

def swapFidelity (w : ℝ) : ℝ := (1+3*w ^ 2)/4

theorem swap_success_probability (w : ℝ) :
    successProbability (swapFidelity w) = (1+w^4)/2 := by
  unfold successProbability swapFidelity; ring

theorem swap_then_purify_sub_elem (w : ℝ) :
    recurrence (swapFidelity w) - elemFidelity w =
      -(w*(1-w)*(3+w+w ^ 2-3*w^3))/(4*(1+w^4)) := by
  have hp : 1+w^4 ≠ 0 := by positivity
  unfold recurrence
  rw [swap_success_probability]
  unfold QuantumBBPSSWDistillation.targetMass swapFidelity elemFidelity
  field_simp [hp]
  ring

theorem swap_then_purify_lt_elem {w : ℝ} (h0 : 0 < w) (h1 : w < 1) :
    recurrence (swapFidelity w) < elemFidelity w := by
  have h3 : w^3 < 1 := pow_lt_one₀ h0.le h1 (by decide)
  have hf : 0 < 3+w+w ^ 2-3*w^3 := by nlinarith [sq_nonneg w]
  have hn : 0 < w*(1-w)*(3+w+w ^ 2-3*w^3) :=
    mul_pos (mul_pos h0 (by linarith)) hf
  have hd : 0 < 4*(1+w^4) := by positivity
  have he := div_neg_of_neg_of_pos (neg_neg_of_pos hn) hd
  rw [← swap_then_purify_sub_elem] at he
  linarith

theorem swap_then_one_purify_sandwich {w : ℝ}
    (h0 : 0 < w) (ht : 1 / 3 < w ^ 2) (h1 : w < 1) :
    swapFidelity w < recurrence (swapFidelity w) ∧
    recurrence (swapFidelity w) < elemFidelity w := by
  have hs : 1/2 < swapFidelity w ∧ swapFidelity w < 1 := by
    unfold swapFidelity; constructor <;> nlinarith
  exact ⟨improves_above_threshold _ hs, swap_then_purify_lt_elem h0 h1⟩

/-- Eventually every depth exceeds the segment fidelity, using independent resources. -/
theorem eventually_purification_exceeds_elem {w : ℝ}
    (h0 : 0 < w) (ht : 1 / 3 < w ^ 2) (h1 : w < 1) :
    ∀ᶠ n in atTop, elemFidelity w < fidelityOrbit (swapFidelity w) n := by
  have hs : 1/2 < swapFidelity w ∧ swapFidelity w ≤ 1 := by
    unfold swapFidelity; constructor <;> nlinarith
  have he : elemFidelity w < 1 := by unfold elemFidelity; linarith
  exact (fidelityOrbit_tendsto_one hs.1 hs.2).eventually (Ioi_mem_nhds he)

theorem exists_purification_depth_exceeding_elemFidelity {w : ℝ}
    (h0 : 0 < w) (ht : 1 / 3 < w ^ 2) (h1 : w < 1) :
    ∃ n : ℕ, elemFidelity w < fidelityOrbit (swapFidelity w) n :=
  (eventually_purification_exceeds_elem h0 ht h1).exists

/-- Convert the existing bounded-visibility matrix to the full-fidelity representation. -/
theorem isotropic_eq_werner (w : Visibility) : isotropic w = werner (elemFidelity w.val) := by
  simp only [isotropic, density, sum_bell, isotropicDistribution, werner, elemFidelity]
  have hs : (1-(1+3*w.val)/4)/3 = (1-w.val)/4 := by ring
  rw [hs]
  simp only [smul_add, add_assoc]

/-- The actual perfect-readout swapping instrument, with its independent spectator memory. -/
def swapOutput {e : Type} [Fintype e] [DecidableEq e]
    (w : Visibility) (σ : EnvironmentState e) : PairDensity :=
  ∑ r, ((wernerRound ⟨1,by norm_num,le_rfl⟩ ⟨1,by norm_num,le_rfl⟩).branch (some r)).map
    ((isotropic w ⊗ₖ isotropic w) ⊗ₖ σ.matrix)

theorem swapOutput_matrix {e : Type} [Fintype e] [DecidableEq e]
    (w : Visibility) (σ : EnvironmentState e) : swapOutput w σ = werner (swapFidelity w.val) := by
  unfold swapOutput
  rw [wernerRound_accepted, isotropic_eq_werner]
  congr 1
  simp only [elemFidelity, swapFidelity, multiplyVisibility, one_mul, pow_two]

/-- Two independently generated swapped pairs feed the existing BBPSSW map. -/
def swapThenPurify {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (w : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) : PairDensity :=
  purified (swapOutput w σ₁ ⊗ₖ swapOutput w σ₂)

theorem swapThenPurify_matrix {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (w : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) :
    swapThenPurify w σ₁ σ₂ = (successProbability (swapFidelity w.val) : ℂ) •
      werner (recurrence (swapFidelity w.val)) := by
  rw [swapThenPurify, swapOutput_matrix, swapOutput_matrix, purified_werner]

theorem swapThenPurify_conditional {e₁ e₂ : Type} [Fintype e₁] [DecidableEq e₁]
    [Fintype e₂] [DecidableEq e₂] (w : Visibility)
    (σ₁ : EnvironmentState e₁) (σ₂ : EnvironmentState e₂) :
    (successProbability (swapFidelity w.val) : ℂ)⁻¹ • swapThenPurify w σ₁ σ₂ =
      werner (recurrence (swapFidelity w.val)) := by
  rw [swapThenPurify_matrix, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (probability_positive _).ne'), one_smul]

structure QuantumHeterogeneousBBPSSWSuite : Prop where
  polynomial : ∀ x y, purified (werner x ⊗ₖ werner y) =
    (heteroTargetMass x y : ℂ) • bellProjector .phiPlus +
      ((heteroSuccessProb x y - heteroTargetMass x y : ℝ)/3 : ℂ) • (1-bellProjector .phiPlus)
  threshold : ∀ x y, 1 / 4 < x → x < 1 → 0 ≤ y ∧ y ≤ 1 →
    (x < heteroRecurrence x y ↔ thresholdFor x < y)
  recovery : ∀ w, 0 < w → 1 / 3 < w ^ 2 → w < 1 →
    ∃ n, elemFidelity w < fidelityOrbit (swapFidelity w) n

theorem verification_suite : QuantumHeterogeneousBBPSSWSuite :=
  ⟨purified_hetero_isotropic, fun _ _ => hetero_strict_improve_left_iff,
    fun _ => exists_purification_depth_exceeding_elemFidelity⟩

end QuantumHeterogeneousBBPSSW

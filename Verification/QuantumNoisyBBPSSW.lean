/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNestedRepeater

/-! Post-depolarization of the entire retained pair after ideal BBPSSW.
This is not noise inside the bilateral CNOT or on the input resources.
Only one-step windows and fixed points are classified; no orbit limit is asserted. -/
noncomputable section
namespace QuantumNoisyBBPSSW
open QuantumCliffordTwirl QuantumBBPSSWDistillation QuantumBBPSSWConvergence
open QuantumCentralDepolarization QuantumGateNoiseComposition QuantumCorrelatedMemoryBSM
open QuantumEntanglementSwappingPurificationContract QuantumRectangularSwapping
open QuantumNoisyBellInstrument QuantumNestedRepeater
open scoped BigOperators ComplexOrder Matrix Kronecker

def noisyPurified (γ : Visibility) (M : FourDensity) : PairDensity :=
  (depolarizing γ).map (purified M)

def noisyRecurrence (γ F : ℝ) : ℝ := (1-γ)/4 + γ*recurrence F

def noisyIncrementQuad (γ F : ℝ) : ℝ := -8*F^2 + 4*(2*γ+1)*F - (5-γ)

def noisyDiscFactor (γ : ℝ) : ℝ := 4*γ^2 + 6*γ - 9

def criticalGamma : ℝ := 3*(Real.sqrt 5-1)/4

def lowerWindowBound (γ : ℝ) : ℝ := (2*γ+1-Real.sqrt (noisyDiscFactor γ))/4

def upperWindowCeiling (γ : ℝ) : ℝ := (2*γ+1+Real.sqrt (noisyDiscFactor γ))/4

theorem noisyRecurrence_sub_self (γ F : ℝ) :
    noisyRecurrence γ F - F = (4*F-1)*noisyIncrementQuad γ F/(36*successProbability F) := by
  have hp := (probability_positive F).ne'
  unfold noisyRecurrence recurrence noisyIncrementQuad
  field_simp
  unfold QuantumBBPSSWDistillation.targetMass successProbability
  ring

theorem noisyRecurrence_bounds {γ F : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    0 ≤ noisyRecurrence γ F ∧ noisyRecurrence γ F ≤ 1 := by
  have hr := recurrence_bounds F ⟨hF0,hF1⟩
  have hmul := mul_le_mul_of_nonneg_left hr.2 hγ0
  unfold noisyRecurrence
  constructor
  · exact add_nonneg (by linarith) (mul_nonneg hγ0 hr.1)
  · nlinarith

theorem noisyRecurrence_quarter (γ : ℝ) : noisyRecurrence γ (1/4) = 1/4 := by
  norm_num [noisyRecurrence, recurrence, QuantumBBPSSWDistillation.targetMass, successProbability]
  ring

theorem noisyRecurrence_one (F : ℝ) : noisyRecurrence 1 F = recurrence F := by
  simp [noisyRecurrence]

theorem noisyRecurrence_zero (F : ℝ) : noisyRecurrence 0 F = 1/4 := by
  simp [noisyRecurrence]

theorem noisyRecurrence_pure_input (γ : ℝ) : noisyRecurrence γ 1 = (1+3*γ)/4 := by
  norm_num [noisyRecurrence, recurrence, QuantumBBPSSWDistillation.targetMass, successProbability]
  ring

theorem criticalGamma_bounds : 1/2 < criticalGamma ∧ criticalGamma < 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  unfold criticalGamma
  constructor <;> nlinarith

theorem noisyDiscFactor_critical : noisyDiscFactor criticalGamma = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold noisyDiscFactor criticalGamma
  nlinarith

theorem noisyDiscFactor_sub (γ δ : ℝ) :
    noisyDiscFactor γ - noisyDiscFactor δ = (γ-δ)*(4*(γ+δ)+6) := by
  unfold noisyDiscFactor
  ring

theorem noisyDiscFactor_neg {γ : ℝ} (h0 : 0 ≤ γ) (hc : γ < criticalGamma) :
    noisyDiscFactor γ < 0 := by
  have he := noisyDiscFactor_sub criticalGamma γ
  rw [noisyDiscFactor_critical] at he
  have hp : 0 < (criticalGamma-γ)*(4*(criticalGamma+γ)+6) :=
    mul_pos (by linarith) (by linarith [criticalGamma_bounds.1])
  linarith

theorem noisyDiscFactor_pos {γ : ℝ} (hc : criticalGamma < γ) :
    0 < noisyDiscFactor γ := by
  have he := noisyDiscFactor_sub γ criticalGamma
  rw [noisyDiscFactor_critical] at he
  have hp : 0 < (γ-criticalGamma)*(4*(γ+criticalGamma)+6) :=
    mul_pos (by linarith) (by linarith [criticalGamma_bounds.1])
  linarith

/-- Completed square exposes all three discriminant regimes without division by the discriminant. -/
theorem noisyIncrementQuad_square (γ F : ℝ) :
    noisyIncrementQuad γ F = (noisyDiscFactor γ - (4*F-(2*γ+1))^2)/2 := by
  unfold noisyIncrementQuad noisyDiscFactor
  ring

theorem noisyRecurrence_fixed_iff_quad (γ F : ℝ) :
    noisyRecurrence γ F = F ↔ F = 1/4 ∨ noisyIncrementQuad γ F = 0 := by
  rw [← sub_eq_zero, noisyRecurrence_sub_self, div_eq_zero_iff]
  have hp : (36 : ℝ)*successProbability F ≠ 0 :=
    (mul_pos (by norm_num) (probability_positive F)).ne'
  simp only [hp, or_false, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr h
  · rintro (rfl | h)
    · left; norm_num
    · exact Or.inr h

theorem noisyRecurrence_strict_decay_below_critical {γ F : ℝ}
    (hγ0 : 0 ≤ γ) (hc : γ < criticalGamma) (hF : 1 / 4 < F) :
    noisyRecurrence γ F < F := by
  have hd := noisyDiscFactor_neg hγ0 hc
  have hq : noisyIncrementQuad γ F < 0 := by
    rw [noisyIncrementQuad_square]; nlinarith [sq_nonneg (4*F-(2*γ+1))]
  have h : noisyRecurrence γ F - F < 0 := by
    rw [noisyRecurrence_sub_self]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hq)
      (mul_pos (by norm_num) (probability_positive F))
  linarith

theorem noisyRecurrence_subcritical_fixed_iff {γ : ℝ}
    (h0 : 0 ≤ γ) (hc : γ < criticalGamma) (F : ℝ) :
    noisyRecurrence γ F = F ↔ F = 1/4 := by
  have hq : noisyIncrementQuad γ F < 0 := by
    rw [noisyIncrementQuad_square]
    nlinarith [noisyDiscFactor_neg h0 hc, sq_nonneg (4*F-(2*γ+1))]
  rw [noisyRecurrence_fixed_iff_quad]
  simp [ne_of_lt hq]

theorem noisyIncrementQuad_critical (F : ℝ) :
    noisyIncrementQuad criticalGamma F = -8*(F-(2*criticalGamma+1)/4)^2 := by
  rw [noisyIncrementQuad_square, noisyDiscFactor_critical]
  ring

theorem noisyRecurrence_critical_no_strict_gain {F : ℝ} (hF : 1 / 4 ≤ F) :
    noisyRecurrence criticalGamma F ≤ F := by
  have hsq := sq_nonneg (F-(2*criticalGamma+1)/4)
  have h : noisyRecurrence criticalGamma F - F ≤ 0 := by
    rw [noisyRecurrence_sub_self, noisyIncrementQuad_critical]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith))
      (mul_nonneg (by norm_num) (probability_positive F).le)
  linarith

theorem noisyRecurrence_critical_fixed_iff (F : ℝ) :
    noisyRecurrence criticalGamma F = F ↔
      F = 1/4 ∨ F = (2*criticalGamma+1)/4 := by
  rw [noisyRecurrence_fixed_iff_quad, noisyIncrementQuad_critical]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right; nlinarith [sq_nonneg (F-(2*criticalGamma+1)/4)]
  · rintro (h | rfl)
    · exact Or.inl h
    · right; ring

theorem noisyIncrementQuad_roots {γ : ℝ} (hd : 0 ≤ noisyDiscFactor γ) (F : ℝ) :
    noisyIncrementQuad γ F = -8*(F-lowerWindowBound γ)*(F-upperWindowCeiling γ) := by
  have hs := Real.sq_sqrt hd
  change Real.sqrt (noisyDiscFactor γ)^2 = 4*γ^2+6*γ-9 at hs
  unfold noisyIncrementQuad lowerWindowBound upperWindowCeiling
  nlinarith [hs]

theorem working_window_inside_half_one {γ : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1) :
    1/2 < lowerWindowBound γ ∧ lowerWindowBound γ < upperWindowCeiling γ ∧
    upperWindowCeiling γ < 1 := by
  have hd := noisyDiscFactor_pos hc
  have hs := Real.sq_sqrt hd.le
  have hp := Real.sqrt_pos.mpr hd
  have hg : 1/2 < γ := lt_trans criticalGamma_bounds.1 hc
  have hl : Real.sqrt (noisyDiscFactor γ) < 2*γ-1 := by
    change Real.sqrt (noisyDiscFactor γ)^2 = 4*γ^2+6*γ-9 at hs
    nlinarith
  have hu : Real.sqrt (noisyDiscFactor γ) < 3-2*γ := by
    change Real.sqrt (noisyDiscFactor γ)^2 = 4*γ^2+6*γ-9 at hs
    nlinarith
  unfold lowerWindowBound upperWindowCeiling
  exact ⟨by linarith, by linarith, by linarith⟩

theorem noisyRecurrence_strict_improve_iff_in_window {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1) (hF : 1 / 4 < F) :
    F < noisyRecurrence γ F ↔ lowerWindowBound γ < F ∧ F < upperWindowCeiling γ := by
  have hd := noisyDiscFactor_pos hc
  have hb := working_window_inside_half_one hc h1
  have hs := noisyRecurrence_sub_self γ F
  rw [noisyIncrementQuad_roots hd.le] at hs
  have hp : 0 < 36*successProbability F := mul_pos (by norm_num) (probability_positive F)
  have he : (noisyRecurrence γ F-F)*(36*successProbability F) =
      (4*F-1)*(-8*(F-lowerWindowBound γ)*(F-upperWindowCeiling γ)) := by
    rw [hs, div_mul_cancel₀ _ hp.ne']
  have hfac : 0 < 4*F-1 := by linarith
  constructor
  · intro hi
    have hprod : (F-lowerWindowBound γ)*(F-upperWindowCeiling γ) < 0 := by
      nlinarith [mul_pos (sub_pos.mpr hi) hp]
    constructor
    · by_contra hn
      have hboth := mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (le_of_not_gt hn))
        (show F-upperWindowCeiling γ ≤ 0 by linarith [hb.2.1])
      linarith
    · by_contra hn
      have hboth := mul_nonneg
        (show 0 ≤ F-lowerWindowBound γ by linarith [hb.2.1])
        (sub_nonneg.mpr (le_of_not_gt hn))
      linarith
  · rintro ⟨hl,hu⟩
    have hprod := mul_neg_of_pos_of_neg (sub_pos.mpr hl) (sub_neg.mpr hu)
    nlinarith [mul_pos hfac (show 0 < -8*((F-lowerWindowBound γ)*
      (F-upperWindowCeiling γ)) by linarith)]

theorem noisyRecurrence_fixed_points_iff {γ F : ℝ}
    (hc : criticalGamma < γ) :
    noisyRecurrence γ F = F ↔
      F = 1/4 ∨ F = lowerWindowBound γ ∨ F = upperWindowCeiling γ := by
  rw [noisyRecurrence_fixed_iff_quad, noisyIncrementQuad_roots (noisyDiscFactor_pos hc).le]
  simp only [mul_eq_zero, neg_eq_zero, OfNat.ofNat_ne_zero, false_or, sub_eq_zero]

theorem critical_window_bounds_coincide :
    lowerWindowBound criticalGamma = (2*criticalGamma+1)/4 ∧
    upperWindowCeiling criticalGamma = (2*criticalGamma+1)/4 := by
  simp [lowerWindowBound, upperWindowCeiling, noisyDiscFactor_critical]

theorem noisyRecurrence_strictMonoOn {γ : ℝ} (hγ : 0 < γ) :
    StrictMonoOn (noisyRecurrence γ) (Set.Icc (1/4 : ℝ) 1) := by
  intro x hx y hy hxy
  have h := mul_lt_mul_of_pos_left (recurrence_strictMonoOn hx hy hxy) hγ
  unfold noisyRecurrence
  linarith

/-- The upper fixed point is distinct from the one-step output of a pure input. -/
theorem ceiling_lt_pure_output {γ : ℝ} (hc : criticalGamma < γ) (h1 : γ < 1) :
    upperWindowCeiling γ < noisyRecurrence γ 1 ∧ noisyRecurrence γ 1 < 1 := by
  have hb := working_window_inside_half_one hc h1
  have hf : noisyRecurrence γ (upperWindowCeiling γ) = upperWindowCeiling γ :=
    (noisyRecurrence_fixed_points_iff hc).mpr (Or.inr (Or.inr rfl))
  have ht := noisyRecurrence_strictMonoOn (show 0 < γ by linarith [criticalGamma_bounds.1])
    (show upperWindowCeiling γ ∈ Set.Icc (1/4 : ℝ) 1 by
      exact ⟨by linarith [hb.1, hb.2.1], hb.2.2.le⟩)
    (show (1 : ℝ) ∈ Set.Icc (1/4) 1 by norm_num) hb.2.2
  rw [hf] at ht
  exact ⟨ht, by rw [noisyRecurrence_pure_input]; linarith⟩

theorem noisyPurified_isCPMap (γ : Visibility) : IsCPMap (noisyPurified γ) := by
  have he : (depolarizing γ).map = weightedFamily (fun _ => (1 : ℝ)) (depolarizing γ).op := by
    funext M
    simp [CPTP.map, weightedFamily]
  apply cp_comp (depolarizing γ).map purified
  · rw [he]
    exact weightedFamily_cp _ (fun _ => by norm_num) _
  · exact purified_cp

theorem noisyPurified_add (γ : Visibility) (M N : FourDensity) :
    noisyPurified γ (M+N) = noisyPurified γ M + noisyPurified γ N := by
  simp only [noisyPurified, purified_add, CPTP.map_add]

theorem noisyPurified_smul (γ : Visibility) (c : ℂ) (M : FourDensity) :
    noisyPurified γ (c • M) = c • noisyPurified γ M := by
  simp only [noisyPurified, purified_smul, CPTP.map_smul]

theorem noisyPurified_trace (γ : Visibility) (M : FourDensity) :
    (noisyPurified γ M).trace = (purified M).trace := (depolarizing γ).trace _

theorem noisyPurified_trace_balance (γ : Visibility) (M : FourDensity) :
    (noisyPurified γ M).trace + (rejected.map M).trace = M.trace := by
  rw [noisyPurified_trace, purified_trace_balance]

theorem noisyPurified_posSemidef (γ : Visibility) {M : FourDensity} (hM : M.PosSemidef) :
    (noisyPurified γ M).PosSemidef := by
  apply (depolarizing γ).positive
  unfold purified twirl
  rw [cycle_family]
  apply weightedFamily_positive _ (fun _ => by norm_num)
  exact weightedFamily_positive _ (fun _ => by norm_num) _ _ (accepted.positive M hM)

/-- The affine fidelity identity holds on all real Werner parameters, not only Visibility inputs. -/
theorem depolarizing_werner (γ : Visibility) (F : ℝ) :
    (depolarizing γ).map (werner F) = werner ((1-γ.val)/4+γ.val*F) := by
  rw [depolarizing_map, werner_trace, one_smul, ← bell_complete]
  simp only [werner, ← Complex.coe_smul, smul_add, add_smul, smul_smul]
  module

theorem noisyPurified_werner (γ : Visibility) (F : ℝ) :
    noisyPurified γ (werner F ⊗ₖ werner F) =
      (successProbability F : ℂ) • werner (noisyRecurrence γ.val F) := by
  rw [noisyPurified, purified_werner, CPTP.map_smul, depolarizing_werner]
  rfl

theorem noisyPurified_success_probability (γ : Visibility) (F : ℝ) :
    (noisyPurified γ (werner F ⊗ₖ werner F)).trace = (successProbability F : ℂ) := by
  rw [noisyPurified_werner, Matrix.trace_smul, werner_trace, smul_eq_mul, mul_one]

theorem noisyPurified_conditional (γ : Visibility) (F : ℝ) :
    (successProbability F : ℂ)⁻¹ • noisyPurified γ (werner F ⊗ₖ werner F) =
      werner (noisyRecurrence γ.val F) := by
  rw [noisyPurified_werner, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (probability_positive F).ne'), one_smul]

theorem noisyPurified_conditional_density (γ : Visibility) {F : ℝ}
    (hF : 0 ≤ F ∧ F ≤ 1) :
    let D := (successProbability F : ℂ)⁻¹ • noisyPurified γ (werner F ⊗ₖ werner F)
    D.PosSemidef ∧ D.trace = 1 := by
  dsimp
  rw [noisyPurified_conditional]
  exact ⟨werner_positive _ (noisyRecurrence_bounds γ.nonnegative γ.le_one hF.1 hF.2),
    werner_trace _⟩

theorem nine_tenths_below_critical : (9/10 : ℝ) < criticalGamma := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  unfold criticalGamma
  nlinarith

theorem nine_tenths_no_working_window {F : ℝ} (hF : 1 / 4 < F) :
    noisyRecurrence (9/10) F < F :=
  noisyRecurrence_strict_decay_below_critical (by norm_num) nine_tenths_below_critical hF

theorem nineteen_twentieths_above_critical : criticalGamma < (19/20 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  unfold criticalGamma
  nlinarith

theorem nineteen_twentieths_ceiling :
    upperWindowCeiling (19/20) = (29+Real.sqrt 31)/40 := by
  have hs : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = 10^2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [upperWindowCeiling, noisyDiscFactor, Real.sqrt_div, hs]
  ring

theorem nineteen_twentieths_working_window_witness :
    noisyRecurrence (19/20) (3/4) = 99/130 ∧
    (3/4 : ℝ) < noisyRecurrence (19/20) (3/4) ∧
    noisyRecurrence (19/20) 1 = 77/80 ∧
    upperWindowCeiling (19/20) = (29+Real.sqrt 31)/40 ∧
    upperWindowCeiling (19/20) < noisyRecurrence (19/20) 1 := by
  refine ⟨?_, ?_, ?_, nineteen_twentieths_ceiling, ?_⟩
  · norm_num [noisyRecurrence, recurrence, QuantumBBPSSWDistillation.targetMass, successProbability]
  · norm_num [noisyRecurrence, recurrence, QuantumBBPSSWDistillation.targetMass, successProbability]
  · norm_num [noisyRecurrence_pure_input]
  · exact (ceiling_lt_pure_output nineteen_twentieths_above_critical (by norm_num)).1

structure QuantumNoisyBBPSSWSuite : Prop where
  operator : ∀ γ F, noisyPurified γ (werner F ⊗ₖ werner F) =
    (successProbability F : ℂ) • werner (noisyRecurrence γ.val F)
  trace : ∀ γ M, (noisyPurified γ M).trace = (purified M).trace
  window : ∀ γ F, criticalGamma < γ → γ < 1 → 1/4 < F →
    (F < noisyRecurrence γ F ↔ lowerWindowBound γ < F ∧ F < upperWindowCeiling γ)
  bounds : ∀ γ, criticalGamma < γ → γ < 1 →
    1/2 < lowerWindowBound γ ∧ lowerWindowBound γ < upperWindowCeiling γ ∧
      upperWindowCeiling γ < 1

theorem verification_suite : QuantumNoisyBBPSSWSuite :=
  ⟨noisyPurified_werner, noisyPurified_trace,
    fun _ _ => noisyRecurrence_strict_improve_iff_in_window,
    fun _ => working_window_inside_half_one⟩

end QuantumNoisyBBPSSW

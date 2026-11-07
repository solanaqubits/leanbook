/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyBBPSSWCritical

/-! All-success binary BBPSSW trees with post-depolarization at every internal node.
Leaves are independently prepared resources. The diagonal preparation is nonlinear;
only each instrument on its full tensor input is a linear CP map. No expected yield,
retry policy or spatially nested noisy repeater is claimed. -/
noncomputable section
namespace QuantumNoisyBBPSSWTree
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence QuantumNoisyBBPSSWCritical
open QuantumBBPSSWDistillation QuantumBBPSSWConvergence QuantumHeterogeneousBBPSSW
open QuantumRepeaterChain QuantumCentralDepolarization QuantumNoisyVisibility
open QuantumEntanglementSwappingPurificationContract QuantumBellDiagonalSwapping
open QuantumBellDiagonalInputs
open Filter Topology
open scoped BigOperators ComplexOrder Matrix Kronecker

def noisyTreeMatrix (γ : Visibility) (F : ℝ) : ℕ → PairDensity
  | 0 => werner F
  | n+1 => noisyPurified γ (noisyTreeMatrix γ F n ⊗ₖ noisyTreeMatrix γ F n)

/-- Weight of the entire tree, not a product of single-path probabilities. -/
def noisyTreeProbability (γ F : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => noisyTreeProbability γ F n ^ 2 * successProbability (noisyOrbit γ F n)

theorem noisyTreeProbability_pos (γ F : ℝ) (n : ℕ) :
    0 < noisyTreeProbability γ F n := by
  induction n with
  | zero => norm_num [noisyTreeProbability]
  | succ n ih => exact mul_pos (pow_pos ih 2) (probability_positive _)

theorem noisyTreeProbability_closed_form (γ F : ℝ) (n : ℕ) :
    noisyTreeProbability γ F n =
      ∏ j ∈ Finset.range n, successProbability (noisyOrbit γ F j) ^ (2 ^ (n-1-j)) := by
  induction n with
  | zero => simp [noisyTreeProbability]
  | succ n ih =>
    rw [noisyTreeProbability, ih, Finset.prod_range_succ, ← Finset.prod_pow]
    have hprod :
        (∏ j ∈ Finset.range n, (successProbability (noisyOrbit γ F j) ^
          (2 ^ (n-1-j))) ^ 2) =
        ∏ j ∈ Finset.range n, successProbability (noisyOrbit γ F j) ^ (2 ^ (n+1-1-j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have he : n+1-1-j = (n-1-j)+1 := by have := Finset.mem_range.mp hj; omega
      rw [← pow_mul, he, pow_succ]
    rw [hprod]
    simp

theorem noisyTreeProbability_two (γ F : ℝ) :
    noisyTreeProbability γ F 2 =
      successProbability F ^ 2 * successProbability (noisyRecurrence γ F) := by
  simp [noisyTreeProbability, noisyOrbit]

theorem noisyTreeProbability_le_one (γ : Visibility) {F : ℝ}
    (h0 : 0 ≤ F) (h1 : F ≤ 1) (n : ℕ) : noisyTreeProbability γ.val F n ≤ 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := (noisyTreeProbability_pos γ.val F n).le
    have hs : noisyTreeProbability γ.val F n ^ 2 ≤ 1 := by nlinarith
    exact mul_le_one₀ hs (probability_positive _).le
      (successProbability_le_one (noisyOrbit_bounds ⟨γ.nonnegative, γ.le_one⟩ ⟨h0,h1⟩ n))

theorem noisyTreeMatrix_eq_werner (γ : Visibility) (F : ℝ) (n : ℕ) :
    noisyTreeMatrix γ F n =
      (noisyTreeProbability γ.val F n : ℂ) • werner (noisyOrbit γ.val F n) := by
  induction n with
  | zero => simp [noisyTreeMatrix, noisyTreeProbability, noisyOrbit]
  | succ n ih =>
    rw [noisyTreeMatrix, ih, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, noisyPurified_smul, noisyPurified_werner, smul_smul, noisyOrbit_succ]
    congr 1
    simp only [noisyTreeProbability, Complex.ofReal_mul, pow_two]

theorem noisyTreeMatrix_trace (γ : Visibility) (F : ℝ) (n : ℕ) :
    (noisyTreeMatrix γ F n).trace = (noisyTreeProbability γ.val F n : ℂ) := by
  rw [noisyTreeMatrix_eq_werner, Matrix.trace_smul, werner_trace, smul_eq_mul, mul_one]

theorem noisyTreeMatrix_posSemidef (γ : Visibility) {F : ℝ}
    (h0 : 0 ≤ F) (h1 : F ≤ 1) (n : ℕ) : (noisyTreeMatrix γ F n).PosSemidef := by
  rw [noisyTreeMatrix_eq_werner, Complex.coe_smul]
  exact (werner_positive _ (noisyOrbit_bounds ⟨γ.nonnegative, γ.le_one⟩ ⟨h0,h1⟩ n)).smul
    (noisyTreeProbability_pos γ.val F n).le

theorem noisyTreeMatrix_conditional (γ : Visibility) (F : ℝ) (n : ℕ) :
    (noisyTreeProbability γ.val F n : ℂ)⁻¹ • noisyTreeMatrix γ F n =
      werner (noisyOrbit γ.val F n) := by
  rw [noisyTreeMatrix_eq_werner, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (noisyTreeProbability_pos γ.val F n).ne'),
    one_smul]

theorem noisyTreeMatrix_conditional_density (γ : Visibility) {F : ℝ}
    (h0 : 0 ≤ F) (h1 : F ≤ 1) (n : ℕ) :
    let D := (noisyTreeProbability γ.val F n : ℂ)⁻¹ • noisyTreeMatrix γ F n
    D.PosSemidef ∧ D.trace = 1 := by
  dsimp
  rw [noisyTreeMatrix_conditional]
  exact ⟨werner_positive _ (noisyOrbit_bounds ⟨γ.nonnegative, γ.le_one⟩ ⟨h0,h1⟩ n),
    werner_trace _⟩

/-- Two independent subtrees are consumed at each node. -/
def noisyTreeInputPairs : ℕ → ℕ
  | 0 => 1
  | n+1 => noisyTreeInputPairs n + noisyTreeInputPairs n

theorem noisyTreeInputPairs_eq (n : ℕ) : noisyTreeInputPairs n = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [noisyTreeInputPairs, ih, pow_succ, Nat.mul_two]

/-- Each leaf of the noisy tree is itself an actual ideal swap of two segment pairs. -/
def swapThenNoisyTree (γ w : Visibility) : ℕ → PairDensity
  | 0 => pairSwap (isotropic w) (isotropic w)
  | n+1 => noisyPurified γ (swapThenNoisyTree γ w n ⊗ₖ swapThenNoisyTree γ w n)

theorem swapThenNoisyTree_eq_noisyTreeMatrix (γ w : Visibility) (n : ℕ) :
    swapThenNoisyTree γ w n = noisyTreeMatrix γ (swapFidelity w.val) n := by
  induction n with
  | zero =>
    change pairSwap (isotropic w) (isotropic w) = werner (swapFidelity w.val)
    rw [pairSwap_isotropic, isotropic_eq_werner]
    congr 1
    simp only [elemFidelity, multiplyVisibility, swapFidelity, pow_two]
  | succ n ih => simp only [swapThenNoisyTree, noisyTreeMatrix, ih]

theorem swapThenNoisyTree_refinement (γ w : Visibility) (n : ℕ) :
    swapThenNoisyTree γ w n =
      (noisyTreeProbability γ.val (swapFidelity w.val) n : ℂ) •
        werner (noisyOrbit γ.val (swapFidelity w.val) n) := by
  rw [swapThenNoisyTree_eq_noisyTreeMatrix, noisyTreeMatrix_eq_werner]

theorem swapThenNoisyTree_conditional (γ w : Visibility) (n : ℕ) :
    (noisyTreeProbability γ.val (swapFidelity w.val) n : ℂ)⁻¹ •
      swapThenNoisyTree γ w n = werner (noisyOrbit γ.val (swapFidelity w.val) n) := by
  rw [swapThenNoisyTree_eq_noisyTreeMatrix, noisyTreeMatrix_conditional]

def swapThenNoisyTreeRawPairs (n : ℕ) : ℕ := 2 * noisyTreeInputPairs n

theorem swapThenNoisyTreeRawPairs_eq (n : ℕ) : swapThenNoisyTreeRawPairs n = 2^(n+1) := by
  simp [swapThenNoisyTreeRawPairs, noisyTreeInputPairs_eq, pow_succ, Nat.mul_comm]

/-- Closed barriers include the stationary lower endpoint. -/
theorem noisyOrbit_le_initial_below_lower {γ F : ℝ}
    (hc : criticalGamma < γ) (hγ : γ < 1) (hq : 1 / 4 < F)
    (hF : F ≤ lowerWindowBound γ) (n : ℕ) : noisyOrbit γ F n ≤ F := by
  rcases hF.lt_or_eq with hF | rfl
  · simpa using (noisyOrbit_strictAnti_between_quarter_and_lower hc hγ hq hF).antitone
      (Nat.zero_le n)
  · exact (noisyOrbit_fixed ((noisyRecurrence_fixed_points_iff hc).mpr
      (Or.inr (Or.inl rfl))) n).le

theorem noisyOrbit_le_initial_above_ceiling {γ F : ℝ}
    (hc : criticalGamma < γ) (hγ : γ < 1) (hF : upperWindowCeiling γ ≤ F)
    (h1 : F ≤ 1) (n : ℕ) : noisyOrbit γ F n ≤ F := by
  rcases hF.lt_or_eq with hF | he
  · simpa using (noisyOrbit_strictAnti_above_ceiling hc hγ hF h1).antitone (Nat.zero_le n)
  · subst F
    exact (noisyOrbit_fixed ((noisyRecurrence_fixed_points_iff hc).mpr
      (Or.inr (Or.inr rfl))) n).le

/-- This finite-depth criterion uses both convergence and no-overshoot barriers. -/
theorem exists_noisy_depth_exceeding_elemFidelity_iff {γ w : ℝ}
    (hw0 : 0 < w) (hw1 : w < 1) (hc : criticalGamma < γ) (hγ : γ < 1) :
    (∃ n : ℕ, elemFidelity w < noisyOrbit γ (swapFidelity w) n) ↔
      lowerWindowBound γ < swapFidelity w ∧ elemFidelity w < upperWindowCeiling γ := by
  have hs : 1 / 4 < swapFidelity w ∧ swapFidelity w < elemFidelity w ∧
      elemFidelity w < 1 := by
    unfold swapFidelity elemFidelity
    have hp : 0 < w^2 := sq_pos_of_pos hw0
    have hw : w^2 < w := by nlinarith
    constructor
    · linarith
    constructor <;> linarith
  constructor
  · rintro ⟨n, hn⟩
    have hlo : lowerWindowBound γ < swapFidelity w := by
      by_contra h
      have hb := noisyOrbit_le_initial_below_lower hc hγ hs.1 (le_of_not_gt h) n
      linarith [hs.2.1]
    refine ⟨hlo, ?_⟩
    by_contra h
    have hceil : upperWindowCeiling γ ≤ elemFidelity w := le_of_not_gt h
    rcases lt_or_ge (swapFidelity w) (upperWindowCeiling γ) with hlt | hge
    · have hb := (noisyOrbit_inside_window hc hγ hlo hlt n).2
      linarith
    · have hb := noisyOrbit_le_initial_above_ceiling hc hγ hge
        (le_trans hs.2.1.le hs.2.2.le) n
      linarith [hs.2.1]
  · rintro ⟨hlo, hceil⟩
    exact ((noisyOrbit_tendsto_ceiling hc hγ hlo
      (le_trans hs.2.1.le hs.2.2.le)).eventually (Ioi_mem_nhds hceil)).exists

def unitVisibility : Visibility := ⟨1, by norm_num, by norm_num⟩
def zeroVisibility : Visibility := ⟨0, by norm_num, by norm_num⟩

theorem noisyOrbit_unit (F : ℝ) (n : ℕ) : noisyOrbit 1 F n = fidelityOrbit F n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [noisyOrbit_succ, fidelityOrbit_succ, noisyRecurrence_one, ih]

theorem noisyTreeProbability_unit (F : ℝ) (n : ℕ) :
    noisyTreeProbability 1 F n = treeProbability F n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [noisyTreeProbability, treeProbability, ih, noisyOrbit_unit]

theorem noisyTreeMatrix_unit (F : ℝ) (n : ℕ) :
    noisyTreeMatrix unitVisibility F n = treeMatrix F n := by
  rw [noisyTreeMatrix_eq_werner, treeMatrix_eq_werner]
  change (noisyTreeProbability 1 F n : ℂ) • werner (noisyOrbit 1 F n) = _
  rw [noisyTreeProbability_unit, noisyOrbit_unit]

theorem noisyTreeMatrix_zero_conditional (F : ℝ) {n : ℕ} (hn : 0 < n) :
    (noisyTreeProbability 0 F n : ℂ)⁻¹ • noisyTreeMatrix zeroVisibility F n =
      werner (1 / 4) := by
  change (noisyTreeProbability zeroVisibility.val F n : ℂ)⁻¹ •
    noisyTreeMatrix zeroVisibility F n = _
  rw [noisyTreeMatrix_conditional]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [show zeroVisibility.val = 0 from rfl, zeroQuality_orbit_succ]

theorem noisyTreeProbability_quarter (γ : ℝ) (n : ℕ) :
    noisyTreeProbability γ (1 / 4) n = (1 / 2 : ℝ) ^ (2^n-1) := by
  induction n with
  | zero => norm_num [noisyTreeProbability]
  | succ n ih =>
    rw [noisyTreeProbability, ih, noisyOrbit_fixed (noisyRecurrence_quarter γ)]
    norm_num [successProbability]
    rw [← pow_mul, ← pow_succ]
    congr 1
    have hp : 0 < (2:ℕ)^n := pow_pos (by decide) n
    simp only [pow_succ]
    omega

theorem nineteen_twentieths_four_fifths_recovery_possible :
    ∃ n : ℕ, elemFidelity (4 / 5) < noisyOrbit (19 / 20) (swapFidelity (4 / 5)) n := by
  apply (exists_noisy_depth_exceeding_elemFidelity_iff (by norm_num) (by norm_num)
    nineteen_twentieths_above_critical (by norm_num)).mpr
  have hn := Real.sqrt_nonneg (noisyDiscFactor (19 / 20))
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 31 by norm_num)
  have h31 := Real.sqrt_nonneg (31:ℝ)
  constructor
  · unfold lowerWindowBound swapFidelity
    linarith
  · rw [nineteen_twentieths_ceiling]
    unfold elemFidelity
    nlinarith

/-- In this witness even equality with the initial segment quality is impossible. -/
theorem nineteen_twentieths_nine_tenths_below_elem (n : ℕ) :
    noisyOrbit (19 / 20) (swapFidelity (9 / 10)) n < elemFidelity (9 / 10) := by
  have hc := nineteen_twentieths_above_critical
  have hn := Real.sqrt_nonneg (noisyDiscFactor (19 / 20))
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 31 by norm_num)
  have h31 := Real.sqrt_nonneg (31:ℝ)
  have hlo : lowerWindowBound (19 / 20) < swapFidelity (9 / 10) := by
    unfold lowerWindowBound swapFidelity
    linarith
  have hhi : swapFidelity (9 / 10) < upperWindowCeiling (19 / 20) := by
    rw [nineteen_twentieths_ceiling]
    unfold swapFidelity
    nlinarith
  have hceil : upperWindowCeiling (19 / 20) < elemFidelity (9 / 10) := by
    rw [nineteen_twentieths_ceiling]
    unfold elemFidelity
    nlinarith
  exact lt_trans (noisyOrbit_inside_window hc (by norm_num) hlo hhi n).2 hceil

theorem nineteen_twentieths_nine_tenths_recovery_impossible :
    ¬ ∃ n : ℕ, elemFidelity (9 / 10) < noisyOrbit (19 / 20) (swapFidelity (9 / 10)) n := by
  rintro ⟨n, hn⟩
  exact (not_lt_of_ge (nineteen_twentieths_nine_tenths_below_elem n).le) hn

structure QuantumNoisyBBPSSWTreeSuite : Prop where
  tree : ∀ γ F n, noisyTreeMatrix γ F n =
    (noisyTreeProbability γ.val F n : ℂ) • werner (noisyOrbit γ.val F n)
  positive_weight : ∀ γ F n, 0 < noisyTreeProbability γ F n
  recovery : ∀ γ w, 0 < w → w < 1 → criticalGamma < γ → γ < 1 →
    ((∃ n, elemFidelity w < noisyOrbit γ (swapFidelity w) n) ↔
      lowerWindowBound γ < swapFidelity w ∧ elemFidelity w < upperWindowCeiling γ)

theorem verification_suite : QuantumNoisyBBPSSWTreeSuite :=
  ⟨noisyTreeMatrix_eq_werner, noisyTreeProbability_pos,
    fun _ _ => exists_noisy_depth_exceeding_elemFidelity_iff⟩

end QuantumNoisyBBPSSWTree

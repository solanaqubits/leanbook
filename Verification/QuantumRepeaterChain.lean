/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumHeterogeneousBBPSSW

/-! Finite ideal repeater with one swapping and one BBPSSW round per level.
Each node consumes four independent child resources. This is a postselected
state construction, not a cloning channel or a model of network scheduling. -/
noncomputable section
namespace QuantumRepeaterChain
open QuantumHeterogeneousBBPSSW QuantumBBPSSWDistillation QuantumBBPSSWConvergence
open QuantumEntanglementSwappingPurificationContract QuantumBellDiagonalInputs
open QuantumBellDiagonalSwapping QuantumSwappingInstrument QuantumNoisyVisibility
open QuantumCentralDepolarization
open scoped BigOperators ComplexOrder Matrix Kronecker

/-- Conditional visibility after swapping two equal pairs and purifying two such outputs. -/
def nodeVisibilityValue (w : ℝ) : ℝ := 2*w^2*(1+2*w^2)/(3*(1+w^4))

def nodeProbability (w : ℝ) : ℝ := (1+w^4)/2

theorem nodeProbability_bounds {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    1/2 ≤ nodeProbability w ∧ nodeProbability w ≤ 1 := by
  have h4 : w^4 ≤ 1 := pow_le_one₀ h0 h1
  unfold nodeProbability
  constructor <;> nlinarith [pow_nonneg h0 4]

theorem nodeProbability_pos (w : ℝ) : 0 < nodeProbability w := by
  unfold nodeProbability
  positivity

theorem nodeVisibility_bounds {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    0 ≤ nodeVisibilityValue w ∧ nodeVisibilityValue w ≤ 1 := by
  have h2 : w^2 ≤ 1 := pow_le_one₀ h0 h1
  have h4 : w^4 ≤ 1 := pow_le_one₀ h0 h1
  have hd : 0 < 3*(1+w^4) := by positivity
  unfold nodeVisibilityValue
  constructor
  · positivity
  · apply (div_le_one hd).mpr
    nlinarith

theorem node_fidelity (w : ℝ) :
    elemFidelity (nodeVisibilityValue w) = recurrence (swapFidelity w) := by
  have hp : 1+w^4 ≠ 0 := by positivity
  unfold recurrence
  rw [swap_success_probability]
  unfold nodeVisibilityValue elemFidelity swapFidelity QuantumBBPSSWDistillation.targetMass
  field_simp [hp]
  ring

theorem node_visibility_strict_decay {w : ℝ} (h0 : 0 < w) (h1 : w < 1) :
    nodeVisibilityValue w < w := by
  have h := swap_then_purify_lt_elem h0 h1
  rw [← node_fidelity] at h
  unfold elemFidelity at h
  linarith

theorem node_visibility_nonincrease {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    nodeVisibilityValue w ≤ w := by
  rcases eq_or_lt_of_le h0 with he | hp
  · rw [← he]; norm_num [nodeVisibilityValue]
  rcases lt_or_eq_of_le h1 with hl | he
  · exact (node_visibility_strict_decay hp hl).le
  · rw [he]; norm_num [nodeVisibilityValue]

def nodeVisibility (w : Visibility) : Visibility :=
  ⟨nodeVisibilityValue w.val, (nodeVisibility_bounds w.nonnegative w.le_one).1,
    (nodeVisibility_bounds w.nonnegative w.le_one).2⟩

def visibilityAt (w : Visibility) : ℕ → Visibility
  | 0 => w
  | k+1 => nodeVisibility (visibilityAt w k)

theorem visibilityAt_recurrence (w : Visibility) (k : ℕ) :
    (visibilityAt w (k+1)).val =
      2*(visibilityAt w k).val^2*(1+2*(visibilityAt w k).val^2)/
        (3*(1+(visibilityAt w k).val^4)) := rfl

theorem visibilityAt_antitone (w : Visibility) : Antitone (fun k => (visibilityAt w k).val) := by
  apply antitone_nat_of_succ_le
  intro k
  exact node_visibility_nonincrease (visibilityAt w k).nonnegative (visibilityAt w k).le_one

theorem visibilityAt_interior {w : Visibility} (h0 : 0 < w.val) (h1 : w.val < 1) (k : ℕ) :
    0 < (visibilityAt w k).val ∧ (visibilityAt w k).val < 1 := by
  induction k with
  | zero => exact ⟨h0,h1⟩
  | succ k ih =>
    change 0 < nodeVisibilityValue _ ∧ nodeVisibilityValue _ < 1
    constructor
    · have hp := ih.1
      unfold nodeVisibilityValue
      positivity
    · exact lt_trans (node_visibility_strict_decay ih.1 ih.2) ih.2

theorem visibilityAt_strictAnti {w : Visibility} (h0 : 0 < w.val) (h1 : w.val < 1) :
    StrictAnti (fun k => (visibilityAt w k).val) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  exact node_visibility_strict_decay (visibilityAt_interior h0 h1 k).1
    (visibilityAt_interior h0 h1 k).2

theorem fidelityAt_recurrence (w : Visibility) (k : ℕ) :
    elemFidelity (visibilityAt w (k+1)).val =
      recurrence (swapFidelity (visibilityAt w k).val) := node_fidelity _

theorem fidelityAt_nonincrease (w : Visibility) (k : ℕ) :
    elemFidelity (visibilityAt w (k+1)).val ≤ elemFidelity (visibilityAt w k).val := by
  have h := visibilityAt_antitone w (Nat.le_succ k)
  unfold elemFidelity
  linarith

/-- Actual ideal BSM instrument on the two adjacent child pairs. -/
def pairSwap (M N : PairDensity) : PairDensity :=
  acceptedMap perfectReadout (M ⊗ₖ N)

theorem pairSwap_isotropic (w v : Visibility) :
    pairSwap (isotropic w) (isotropic v) = isotropic (multiplyVisibility w v) := by
  unfold pairSwap isotropic
  rw [← input_density_tensor, ideal_accepted, isotropic_visibility_product]
  rfl

theorem pairSwap_common_smul (c : ℂ) (M : PairDensity) :
    pairSwap (c • M) (c • M) = c^2 • pairSwap M M := by
  unfold pairSwap
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, accepted_smul, pow_two]

/-- Four independently prepared children: two swaps, then a destructive purification. -/
def repeaterNode (A B C D : PairDensity) : PairDensity :=
  purified (pairSwap A B ⊗ₖ pairSwap C D)

theorem repeaterNode_isotropic (w : Visibility) :
    repeaterNode (isotropic w) (isotropic w) (isotropic w) (isotropic w) =
      (nodeProbability w.val : ℂ) • isotropic (nodeVisibility w) := by
  rw [repeaterNode, pairSwap_isotropic, isotropic_eq_werner]
  have hs : elemFidelity (multiplyVisibility w w).val = swapFidelity w.val := by
    simp only [elemFidelity, multiplyVisibility, swapFidelity, pow_two]
  rw [hs, purified_werner, isotropic_eq_werner]
  change (successProbability (swapFidelity w.val) : ℂ) • _ =
    (nodeProbability w.val : ℂ) • werner (elemFidelity (nodeVisibilityValue w.val))
  rw [node_fidelity, swap_success_probability]
  rfl

theorem repeaterNode_common_smul (c : ℂ) (M : PairDensity) :
    repeaterNode (c • M) (c • M) (c • M) (c • M) =
      c^4 • repeaterNode M M M M := by
  unfold repeaterNode
  rw [pairSwap_common_smul, Matrix.smul_kronecker, Matrix.kronecker_smul,
    smul_smul, purified_smul]
  congr 1
  ring

/-- Unnormalized all-success state, without early conditioning. -/
def repeaterMatrix (w : Visibility) : ℕ → PairDensity
  | 0 => isotropic w
  | k+1 => repeaterNode (repeaterMatrix w k) (repeaterMatrix w k)
      (repeaterMatrix w k) (repeaterMatrix w k)

def repeaterProbability (w : Visibility) : ℕ → ℝ
  | 0 => 1
  | k+1 => repeaterProbability w k ^ 4 * nodeProbability (visibilityAt w k).val

theorem repeaterProbability_pos (w : Visibility) (k : ℕ) : 0 < repeaterProbability w k := by
  induction k with
  | zero => norm_num [repeaterProbability]
  | succ k ih => exact mul_pos (pow_pos ih 4) (nodeProbability_pos _)

theorem repeaterProbability_le_one (w : Visibility) (k : ℕ) : repeaterProbability w k ≤ 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact mul_le_one₀ (pow_le_one₀ (repeaterProbability_pos w k).le ih)
      (nodeProbability_pos _).le
      (nodeProbability_bounds (visibilityAt w k).nonnegative (visibilityAt w k).le_one).2

theorem repeaterProbability_closed_form (w : Visibility) (k : ℕ) :
    repeaterProbability w k = ∏ j ∈ Finset.range k,
      nodeProbability (visibilityAt w j).val ^ (4^(k-1-j)) := by
  induction k with
  | zero => simp [repeaterProbability]
  | succ k ih =>
    rw [repeaterProbability, ih, Finset.prod_range_succ, ← Finset.prod_pow]
    have hprod : (∏ j ∈ Finset.range k,
        (nodeProbability (visibilityAt w j).val ^ (4^(k-1-j)))^4) =
        ∏ j ∈ Finset.range k, nodeProbability (visibilityAt w j).val ^ (4^(k+1-1-j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have he : k+1-1-j = (k-1-j)+1 := by have := Finset.mem_range.mp hj; omega
      rw [← pow_mul, he, pow_succ]
    rw [hprod]
    simp

theorem repeaterMatrix_refinement (w : Visibility) (k : ℕ) :
    repeaterMatrix w k = (repeaterProbability w k : ℂ) • isotropic (visibilityAt w k) := by
  induction k with
  | zero => simp [repeaterMatrix, repeaterProbability, visibilityAt]
  | succ k ih =>
    rw [repeaterMatrix, ih, repeaterNode_common_smul, repeaterNode_isotropic, smul_smul]
    simp only [repeaterProbability, visibilityAt, Complex.ofReal_mul, Complex.ofReal_pow]

theorem repeaterMatrix_positive (w : Visibility) (k : ℕ) : (repeaterMatrix w k).PosSemidef := by
  rw [repeaterMatrix_refinement, Complex.coe_smul]
  exact (density_positive _).smul (repeaterProbability_pos w k).le

theorem repeaterMatrix_trace (w : Visibility) (k : ℕ) :
    (repeaterMatrix w k).trace = (repeaterProbability w k : ℂ) := by
  rw [repeaterMatrix_refinement, Matrix.trace_smul, isotropic_trace, smul_eq_mul, mul_one]

theorem repeaterMatrix_conditional (w : Visibility) (k : ℕ) :
    (repeaterProbability w k : ℂ)⁻¹ • repeaterMatrix w k = isotropic (visibilityAt w k) := by
  rw [repeaterMatrix_refinement, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (repeaterProbability_pos w k).ne'), one_smul]

theorem repeaterMatrix_conditional_density (w : Visibility) (k : ℕ) :
    let M := (repeaterProbability w k : ℂ)⁻¹ • repeaterMatrix w k
    M.PosSemidef ∧ M.trace = 1 := by
  dsimp
  rw [repeaterMatrix_conditional]
  exact ⟨density_positive _, isotropic_trace _⟩

theorem repeaterMatrix_conditional_fidelity (w : Visibility) (k : ℕ) :
    (targetOverlap ((repeaterProbability w k : ℂ)⁻¹ • repeaterMatrix w k)).re =
      elemFidelity (visibilityAt w k).val := by
  rw [repeaterMatrix_conditional]
  simp [isotropic, density_overlap, isotropicDistribution, elemFidelity]

/-- Spatial span doubles, while four independently generated children are consumed. -/
def segmentCount : ℕ → ℕ | 0 => 1 | k+1 => 2*segmentCount k

def rawPairCount : ℕ → ℕ | 0 => 1 | k+1 => 4*rawPairCount k

theorem segmentCount_eq (k : ℕ) : segmentCount k = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [segmentCount, ih, pow_succ]; omega

theorem rawPairCount_eq (k : ℕ) : rawPairCount k = 4^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [rawPairCount, ih, pow_succ]; omega

theorem rawPairCount_per_segment (k : ℕ) : rawPairCount k = segmentCount k * 2^k := by
  rw [rawPairCount_eq, segmentCount_eq, ← mul_pow]
  norm_num

structure QuantumRepeaterChainSuite : Prop where
  refinement : ∀ w k, repeaterMatrix w k =
    (repeaterProbability w k : ℂ) • isotropic (visibilityAt w k)
  positive : ∀ w k, (repeaterMatrix w k).PosSemidef
  trace : ∀ w k, (repeaterMatrix w k).trace = (repeaterProbability w k : ℂ)
  nonincrease : ∀ w k, elemFidelity (visibilityAt w (k+1)).val ≤
    elemFidelity (visibilityAt w k).val
  resources : ∀ k, rawPairCount k = segmentCount k * 2^k

theorem verification_suite : QuantumRepeaterChainSuite :=
  ⟨repeaterMatrix_refinement, repeaterMatrix_positive, repeaterMatrix_trace,
    fidelityAt_nonincrease, rawPairCount_per_segment⟩

end QuantumRepeaterChain

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumRepeaterChain

/-! One-round repeater decay and finite nested purification trees.
Quality statements are conditional on all internal nodes succeeding. No limit
at one, expected yield, retries or arbitrary correlated resources are asserted. -/
noncomputable section
namespace QuantumNestedRepeater
open QuantumCliffordTwirl QuantumBBPSSWDistillation QuantumBBPSSWConvergence
open QuantumHeterogeneousBBPSSW QuantumRepeaterChain QuantumBellDiagonalSwapping
open QuantumEntanglementSwappingPurificationContract QuantumCentralDepolarization
open QuantumBellDiagonalInputs QuantumNoisyVisibility
open Filter Topology
open scoped BigOperators ComplexOrder Matrix Kronecker

theorem nodeVisibilityValue_loss_factorization (w : ℝ) :
    w - nodeVisibilityValue w =
      w*(1-w)*(3+w+w^2-3*w^3)/(3*(1+w^4)) := by
  unfold nodeVisibilityValue
  field_simp
  ring

theorem nodeVisibilityValue_sub_sq_factorization (w : ℝ) :
    nodeVisibilityValue w - w^2 = w^2*(1-w^2)*(3*w^2-1)/(3*(1+w^4)) := by
  unfold nodeVisibilityValue
  field_simp
  ring

theorem nodeVisibilityValue_between_sq_and_self {w : ℝ}
    (h0 : 0 < w) (ht : 1 / 3 < w ^ 2) (h1 : w < 1) :
    w^2 < nodeVisibilityValue w ∧ nodeVisibilityValue w < w := by
  have hsq : w^2 < 1 := by nlinarith
  have hg : 0 < nodeVisibilityValue w - w^2 := by
    rw [nodeVisibilityValue_sub_sq_factorization]
    exact div_pos (mul_pos (mul_pos (by nlinarith) (by linarith)) (by linarith))
      (by positivity)
  exact ⟨by linarith, node_visibility_strict_decay h0 h1⟩

/-- A first-step benefit does not imply domination of the entire pure-swapping orbit. -/
theorem three_fifths_two_step_swap_reversal :
    (1/3 : ℝ) < (3/5 : ℝ)^2 ∧
    nodeVisibilityValue (3/5) = 129/353 ∧
    (3/5 : ℝ)^2 < nodeVisibilityValue (3/5) ∧
    nodeVisibilityValue (nodeVisibilityValue (3/5)) = 875821377/7902162881 ∧
    nodeVisibilityValue (nodeVisibilityValue (3/5)) < (3/5 : ℝ)^4 := by
  norm_num [nodeVisibilityValue]

theorem nodeVisibilityValue_fixed_iff {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    nodeVisibilityValue w = w ↔ w = 0 ∨ w = 1 := by
  constructor
  · intro h
    by_cases hz : w = 0
    · exact Or.inl hz
    by_cases ho : w = 1
    · exact Or.inr ho
    have := node_visibility_strict_decay (lt_of_le_of_ne h0 (Ne.symm hz))
      (lt_of_le_of_ne h1 ho)
    linarith
  · rintro (rfl | rfl) <;> norm_num [nodeVisibilityValue]

theorem continuous_nodeVisibilityValue : Continuous nodeVisibilityValue := by
  have hn : Continuous (fun w : ℝ => 2*w^2*(1+2*w^2)) := by fun_prop
  have hd : Continuous (fun w : ℝ => 3*(1+w^4)) := by fun_prop
  exact hn.div hd (fun _ => by positivity)

theorem visibilityAt_tendsto_zero (w : Visibility) (h1 : w.val < 1) :
    Tendsto (fun k : ℕ => (visibilityAt w k).val) atTop (nhds 0) := by
  let a : ℕ → ℝ := fun k => (visibilityAt w k).val
  have hm : Antitone a := visibilityAt_antitone w
  have hb : BddBelow (Set.range a) :=
    ⟨0, by rintro _ ⟨n,rfl⟩; exact (visibilityAt w n).nonnegative⟩
  have ht := tendsto_atTop_ciInf hm hb
  have hlo : 0 ≤ ⨅ n, a n := le_ciInf (fun n => (visibilityAt w n).nonnegative)
  have hhi : (⨅ n, a n) ≤ w.val := by simpa [a, visibilityAt] using ciInf_le hb 0
  have hs : Tendsto (fun n => a (n+1)) atTop (nhds (⨅ n, a n)) :=
    (tendsto_add_atTop_iff_nat 1).mpr ht
  have hc := continuous_nodeVisibilityValue.continuousAt.tendsto.comp ht
  have he : (fun n => a (n+1)) = fun n => nodeVisibilityValue (a n) := rfl
  rw [he] at hs
  have hf := tendsto_nhds_unique hc hs
  rcases (nodeVisibilityValue_fixed_iff hlo (by linarith)).mp hf with hz | ho
  · rwa [hz] at ht
  · linarith

theorem elemFidelity_visibilityAt_tendsto_quarter (w : Visibility) (h1 : w.val < 1) :
    Tendsto (fun k => elemFidelity (visibilityAt w k).val) atTop (nhds (1/4)) := by
  have hc : Continuous elemFidelity := by unfold elemFidelity; fun_prop
  simpa [Function.comp_def, elemFidelity] using
    hc.continuousAt.tendsto.comp (visibilityAt_tendsto_zero w h1)

/-- Monotonicity in the input, distinct from monotonicity along a purification orbit. -/
theorem recurrence_strictMonoOn : StrictMonoOn recurrence (Set.Icc (1/4 : ℝ) 1) := by
  intro x hx y hy hxy
  have hp : 0 < -24*x*y+42*x+42*y-6 := by
    have hm : 0 ≤ x*(1-y) := mul_nonneg (by linarith [hx.1]) (by linarith [hy.2])
    nlinarith [hx.1, hy.1]
  have he : QuantumBBPSSWDistillation.targetMass y * successProbability x -
      QuantumBBPSSWDistillation.targetMass x * successProbability y =
      (y-x)*(-24*x*y+42*x+42*y-6)/81 := by
    unfold QuantumBBPSSWDistillation.targetMass successProbability
    ring
  have hd : 0 < (y-x)*(-24*x*y+42*x+42*y-6)/81 :=
    div_pos (mul_pos (sub_pos.mpr hxy) hp) (by norm_num)
  exact (div_lt_div_iff₀ (probability_positive x) (probability_positive y)).mpr
    (by linarith)

theorem recurrence_quarter_bounds {F : ℝ} (h : 1 / 4 ≤ F ∧ F ≤ 1) :
    1/4 ≤ recurrence F ∧ recurrence F ≤ 1 := by
  have hlo := recurrence_strictMonoOn.monotoneOn (show (1/4 : ℝ) ∈ Set.Icc (1/4) 1 by
    norm_num) h h.1
  have hhi := recurrence_strictMonoOn.monotoneOn h
    (show (1 : ℝ) ∈ Set.Icc (1/4) 1 by norm_num) h.2
  norm_num [recurrence, QuantumBBPSSWDistillation.targetMass, successProbability] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem fidelityOrbit_quarter_bounds {F : ℝ} (h : 1 / 4 ≤ F ∧ F ≤ 1) (m : ℕ) :
    1/4 ≤ fidelityOrbit F m ∧ fidelityOrbit F m ≤ 1 := by
  induction m with
  | zero => exact h
  | succ m ih => rw [fidelityOrbit_succ]; exact recurrence_quarter_bounds ih

theorem fidelityOrbit_strictMonoOn (m : ℕ) :
    StrictMonoOn (fun F => fidelityOrbit F m) (Set.Icc (1/4 : ℝ) 1) := by
  intro x hx y hy hxy
  induction m with
  | zero => exact hxy
  | succ m ih =>
    dsimp only at ih ⊢
    rw [fidelityOrbit_succ, fidelityOrbit_succ]
    exact recurrence_strictMonoOn (fidelityOrbit_quarter_bounds hx m)
      (fidelityOrbit_quarter_bounds hy m) ih

def nestedNodeVisibilityValue (m : ℕ) (w : ℝ) : ℝ :=
  (4*fidelityOrbit (swapFidelity w) m-1)/3

theorem nestedNodeVisibility_bounds (m : ℕ) {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) :
    0 ≤ nestedNodeVisibilityValue m w ∧ nestedNodeVisibilityValue m w ≤ 1 := by
  have hs : 1/4 ≤ swapFidelity w ∧ swapFidelity w ≤ 1 := by
    have := pow_le_one₀ h0 h1 (n := 2)
    unfold swapFidelity
    constructor <;> nlinarith [sq_nonneg w]
  have hf := fidelityOrbit_quarter_bounds hs m
  unfold nestedNodeVisibilityValue
  constructor <;> linarith

def nestedNodeVisibility (m : ℕ) (w : Visibility) : Visibility :=
  ⟨nestedNodeVisibilityValue m w.val, (nestedNodeVisibility_bounds m w.nonnegative w.le_one).1,
    (nestedNodeVisibility_bounds m w.nonnegative w.le_one).2⟩

def nestedVisibilityAt (m : ℕ) (w : Visibility) : ℕ → Visibility
  | 0 => w
  | k+1 => nestedNodeVisibility m (nestedVisibilityAt m w k)

theorem nestedNodeVisibility_strictMonoOn (m : ℕ) :
    StrictMonoOn (nestedNodeVisibilityValue m) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hb (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      swapFidelity z ∈ Set.Icc (1/4 : ℝ) 1 := by
    have := pow_le_one₀ hz.1 hz.2 (n := 2)
    unfold swapFidelity
    constructor <;> nlinarith [sq_nonneg z]
  have hsq : swapFidelity x < swapFidelity y := by
    unfold swapFidelity
    have hp : 0 < (y-x)*(y+x) := mul_pos (by linarith) (by linarith [hx.1])
    nlinarith
  have hf := fidelityOrbit_strictMonoOn m (hb x hx) (hb y hy) hsq
  unfold nestedNodeVisibilityValue
  linarith

theorem nestedVisibilityAt_strictMono_of_first_step_gain (m : ℕ) (w : Visibility)
    (hg : w.val < (nestedVisibilityAt m w 1).val) :
    StrictMono (fun k => (nestedVisibilityAt m w k).val) := by
  apply strictMono_nat_of_lt_succ
  intro k
  induction k with
  | zero => exact hg
  | succ k ih =>
    exact nestedNodeVisibility_strictMonoOn m
      ⟨(nestedVisibilityAt m w k).nonnegative, (nestedVisibilityAt m w k).le_one⟩
      ⟨(nestedVisibilityAt m w (k+1)).nonnegative, (nestedVisibilityAt m w (k+1)).le_one⟩ ih

theorem nestedVisibilityAt_sustains_initial_quality (m : ℕ) (w : Visibility)
    (hg : w.val < (nestedVisibilityAt m w 1).val) {k : ℕ} (hk : 0 < k) :
    w.val < (nestedVisibilityAt m w k).val ∧
    elemFidelity w.val < elemFidelity (nestedVisibilityAt m w k).val := by
  have h := nestedVisibilityAt_strictMono_of_first_step_gain m w hg hk
  change w.val < _ at h
  exact ⟨h, by unfold elemFidelity; linarith⟩

def fourFifthsVisibility : Visibility := ⟨4/5, by norm_num, by norm_num⟩

theorem fourFifths_depth_four_gain :
    fourFifthsVisibility.val < (nestedVisibilityAt 4 fourFifthsVisibility 1).val := by
  norm_num [nestedVisibilityAt, nestedNodeVisibility, nestedNodeVisibilityValue,
    fourFifthsVisibility, fidelityOrbit, Function.iterate_succ_apply', swapFidelity,
    recurrence, QuantumBBPSSWDistillation.targetMass, successProbability]

theorem nestedRepeater_four_fifths_depth_four_sustains {k : ℕ} (hk : 0 < k) :
    (4/5 : ℝ) < (nestedVisibilityAt 4 fourFifthsVisibility k).val ∧
    (17/20 : ℝ) < elemFidelity (nestedVisibilityAt 4 fourFifthsVisibility k).val := by
  have h := nestedVisibilityAt_sustains_initial_quality 4 fourFifthsVisibility
    fourFifths_depth_four_gain hk
  norm_num [fourFifthsVisibility, elemFidelity] at h ⊢
  exact h

/-- The upper endpoint cannot be reached at a finite level of a strictly growing orbit. -/
theorem nestedVisibilityAt_lt_one_of_gain (m : ℕ) (w : Visibility)
    (hg : w.val < (nestedVisibilityAt m w 1).val) (k : ℕ) :
    (nestedVisibilityAt m w k).val < 1 :=
  lt_of_lt_of_le (nestedVisibilityAt_strictMono_of_first_step_gain m w hg (Nat.lt_succ_self k))
    (nestedVisibilityAt m w (k+1)).le_one

/-- Independent copies at the leaves, not a single-input cloning channel. -/
def purifiedTree : ℕ → PairDensity → PairDensity
  | 0, M => M
  | m+1, M => purified (purifiedTree m M ⊗ₖ purifiedTree m M)

theorem purifiedTree_smul (m : ℕ) (c : ℂ) (M : PairDensity) :
    purifiedTree m (c • M) = c^(2^m) • purifiedTree m M := by
  induction m with
  | zero => simp [purifiedTree]
  | succ m ih =>
    rw [purifiedTree, ih, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, purified_smul]
    rw [← pow_add, pow_succ]
    congr 2
    omega

theorem purifiedTree_werner (m : ℕ) (F : ℝ) :
    purifiedTree m (werner F) = treeMatrix F m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [purifiedTree, treeMatrix, ih]

def nestedRepeaterStep (m : ℕ) (D : PairDensity) : PairDensity :=
  purifiedTree m (pairSwap D D)

def nestedRepeaterMatrix (m : ℕ) (w : Visibility) : ℕ → PairDensity
  | 0 => isotropic w
  | k+1 => nestedRepeaterStep m (nestedRepeaterMatrix m w k)

def nestedNodeProbability (m : ℕ) (w : ℝ) : ℝ :=
  treeProbability (swapFidelity w) m

def nestedBranchFactor (m : ℕ) : ℕ := 2^(m+1)

def nestedRepeaterProbability (m : ℕ) (w : Visibility) : ℕ → ℝ
  | 0 => 1
  | k+1 => nestedRepeaterProbability m w k ^ nestedBranchFactor m *
      nestedNodeProbability m (nestedVisibilityAt m w k).val

def nestedRawPairCount (m k : ℕ) : ℕ := nestedBranchFactor m ^ k

theorem nestedNode_fidelity (m : ℕ) (w : ℝ) :
    elemFidelity (nestedNodeVisibilityValue m w) = fidelityOrbit (swapFidelity w) m := by
  unfold elemFidelity nestedNodeVisibilityValue
  ring

theorem nestedRepeaterStep_smul (m : ℕ) (c : ℂ) (D : PairDensity) :
    nestedRepeaterStep m (c • D) = c^nestedBranchFactor m • nestedRepeaterStep m D := by
  unfold nestedRepeaterStep
  rw [pairSwap_common_smul, purifiedTree_smul, ← pow_mul]
  have he : 2*2^m = nestedBranchFactor m := by
    simp only [nestedBranchFactor, pow_succ, Nat.mul_comm]
  rw [he]

theorem nestedRepeaterStep_isotropic (m : ℕ) (w : Visibility) :
    nestedRepeaterStep m (isotropic w) =
      (nestedNodeProbability m w.val : ℂ) • isotropic (nestedNodeVisibility m w) := by
  rw [nestedRepeaterStep, pairSwap_isotropic, isotropic_eq_werner]
  have hs : elemFidelity (multiplyVisibility w w).val = swapFidelity w.val := by
    simp only [elemFidelity, multiplyVisibility, swapFidelity, pow_two]
  rw [hs, purifiedTree_werner, treeMatrix_eq_werner, isotropic_eq_werner]
  change _ = (nestedNodeProbability m w.val : ℂ) •
    werner (elemFidelity (nestedNodeVisibilityValue m w.val))
  rw [nestedNode_fidelity]
  rfl

theorem nestedNodeProbability_pos (m : ℕ) (w : ℝ) : 0 < nestedNodeProbability m w :=
  treeProbability_pos _ _

theorem nestedNodeProbability_le_one (m : ℕ) (w : Visibility) :
    nestedNodeProbability m w.val ≤ 1 := by
  have h2 : w.val^2 ≤ 1 := pow_le_one₀ w.nonnegative w.le_one
  apply treeProbability_le_one
  unfold swapFidelity
  constructor <;> nlinarith [sq_nonneg w.val]

theorem nestedRepeaterProbability_pos (m : ℕ) (w : Visibility) (k : ℕ) :
    0 < nestedRepeaterProbability m w k := by
  induction k with
  | zero => norm_num [nestedRepeaterProbability]
  | succ k ih => exact mul_pos (pow_pos ih _) (nestedNodeProbability_pos _ _)

theorem nestedRepeaterProbability_le_one (m : ℕ) (w : Visibility) (k : ℕ) :
    nestedRepeaterProbability m w k ≤ 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact mul_le_one₀ (pow_le_one₀ (nestedRepeaterProbability_pos m w k).le ih)
      (nestedNodeProbability_pos _ _).le (nestedNodeProbability_le_one _ _)

theorem nestedRepeaterMatrix_refinement (m : ℕ) (w : Visibility) (k : ℕ) :
    nestedRepeaterMatrix m w k =
      (nestedRepeaterProbability m w k : ℂ) • isotropic (nestedVisibilityAt m w k) := by
  induction k with
  | zero => simp [nestedRepeaterMatrix, nestedRepeaterProbability, nestedVisibilityAt]
  | succ k ih =>
    rw [nestedRepeaterMatrix, ih, nestedRepeaterStep_smul, nestedRepeaterStep_isotropic, smul_smul]
    simp only [nestedRepeaterProbability, nestedVisibilityAt, Complex.ofReal_mul,
      Complex.ofReal_pow]

theorem nestedRepeaterMatrix_positive (m : ℕ) (w : Visibility) (k : ℕ) :
    (nestedRepeaterMatrix m w k).PosSemidef := by
  rw [nestedRepeaterMatrix_refinement, Complex.coe_smul]
  exact (density_positive _).smul (nestedRepeaterProbability_pos m w k).le

theorem nestedRepeaterMatrix_trace (m : ℕ) (w : Visibility) (k : ℕ) :
    (nestedRepeaterMatrix m w k).trace = (nestedRepeaterProbability m w k : ℂ) := by
  rw [nestedRepeaterMatrix_refinement, Matrix.trace_smul, isotropic_trace, smul_eq_mul, mul_one]

theorem nestedRepeaterMatrix_conditional (m : ℕ) (w : Visibility) (k : ℕ) :
    (nestedRepeaterProbability m w k : ℂ)⁻¹ • nestedRepeaterMatrix m w k =
      isotropic (nestedVisibilityAt m w k) := by
  rw [nestedRepeaterMatrix_refinement, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (nestedRepeaterProbability_pos m w k).ne'),
    one_smul]

theorem nestedRepeaterMatrix_conditional_density (m : ℕ) (w : Visibility) (k : ℕ) :
    let M := (nestedRepeaterProbability m w k : ℂ)⁻¹ • nestedRepeaterMatrix m w k
    M.PosSemidef ∧ M.trace = 1 := by
  dsimp
  rw [nestedRepeaterMatrix_conditional]
  exact ⟨density_positive _, isotropic_trace _⟩

theorem nestedRepeaterMatrix_conditional_fidelity (m : ℕ) (w : Visibility) (k : ℕ) :
    (targetOverlap ((nestedRepeaterProbability m w k : ℂ)⁻¹ •
      nestedRepeaterMatrix m w k)).re = elemFidelity (nestedVisibilityAt m w k).val := by
  rw [nestedRepeaterMatrix_conditional]
  simp [isotropic, density_overlap, isotropicDistribution, elemFidelity]

theorem nestedRawPairCount_eq (m k : ℕ) : nestedRawPairCount m k = 2^((m+1)*k) := by
  simp only [nestedRawPairCount, nestedBranchFactor, pow_mul]

theorem nestedRawPairCount_per_segment (m k : ℕ) :
    nestedRawPairCount m k = segmentCount k * 2^(m*k) := by
  rw [nestedRawPairCount_eq, segmentCount_eq, ← pow_add]
  congr 1
  ring

/-- Zero purification rounds recover ideal swapping, with no selection loss. -/
theorem nestedNodeVisibilityValue_zero (w : ℝ) : nestedNodeVisibilityValue 0 w = w^2 := by
  simp only [nestedNodeVisibilityValue, fidelityOrbit_zero, swapFidelity]
  ring

theorem nestedVisibilityAt_zero (w : Visibility) (k : ℕ) :
    (nestedVisibilityAt 0 w k).val = w.val^(2^k) := by
  induction k with
  | zero => simp [nestedVisibilityAt]
  | succ k ih =>
    change nestedNodeVisibilityValue 0 _ = _
    rw [nestedNodeVisibilityValue_zero, ih, ← pow_mul, pow_succ]

theorem nestedRepeaterProbability_zero (w : Visibility) (k : ℕ) :
    nestedRepeaterProbability 0 w k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [nestedRepeaterProbability, ih, nestedNodeProbability, treeProbability]

/-- One purification round recovers the earlier operator definition literally. -/
theorem nestedRepeaterStep_one (D : PairDensity) :
    nestedRepeaterStep 1 D = repeaterNode D D D D := rfl

theorem nestedRepeaterMatrix_one (w : Visibility) (k : ℕ) :
    nestedRepeaterMatrix 1 w k = repeaterMatrix w k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [nestedRepeaterMatrix, ih, nestedRepeaterStep_one, repeaterMatrix]

theorem nestedNodeVisibilityValue_one (w : ℝ) :
    nestedNodeVisibilityValue 1 w = nodeVisibilityValue w := by
  have h := node_fidelity w
  simp only [nestedNodeVisibilityValue, fidelityOrbit_succ, fidelityOrbit_zero]
  unfold elemFidelity at h
  linarith

theorem nestedVisibilityAt_one (w : Visibility) (k : ℕ) :
    (nestedVisibilityAt 1 w k).val = (visibilityAt w k).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change nestedNodeVisibilityValue 1 _ = nodeVisibilityValue _
    rw [nestedNodeVisibilityValue_one, ih]

theorem nestedRepeaterProbability_one (w : Visibility) (k : ℕ) :
    nestedRepeaterProbability 1 w k = repeaterProbability w k := by
  have h := congrArg Matrix.trace (nestedRepeaterMatrix_one w k)
  rw [nestedRepeaterMatrix_trace, repeaterMatrix_trace] at h
  exact Complex.ofReal_injective h

structure QuantumNestedRepeaterSuite : Prop where
  decay : ∀ w : Visibility, w.val < 1 →
    Tendsto (fun k => (visibilityAt w k).val) atTop (nhds 0)
  refinement : ∀ m w k, nestedRepeaterMatrix m w k =
    (nestedRepeaterProbability m w k : ℂ) • isotropic (nestedVisibilityAt m w k)
  growth : ∀ m w, w.val < (nestedVisibilityAt m w 1).val →
    StrictMono (fun k => (nestedVisibilityAt m w k).val)
  resources : ∀ m k, nestedRawPairCount m k = 2^((m+1)*k)

theorem verification_suite : QuantumNestedRepeaterSuite :=
  ⟨visibilityAt_tendsto_zero, nestedRepeaterMatrix_refinement,
    nestedVisibilityAt_strictMono_of_first_step_gain, nestedRawPairCount_eq⟩

end QuantumNestedRepeater

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyBBPSSWTree

/-! Chronological spatial repeater schedules with fixed output-pair post-depolarization.
Each level uses independent copies of the preceding resource; its weight counts
success of every internal node. Ideal swapping, no early normalization, no retry
yield or unconditional quality guarantee. -/
noncomputable section
namespace QuantumScheduledNoisyRepeater
open QuantumRectangularSwapping
open QuantumNoisyBBPSSWTree QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence
open QuantumNestedRepeater QuantumRepeaterChain QuantumHeterogeneousBBPSSW
open QuantumBBPSSWDistillation QuantumBBPSSWConvergence QuantumCentralDepolarization
open QuantumBellDiagonalSwapping QuantumBellDiagonalInputs QuantumNoisyVisibility
open QuantumEntanglementSwappingPurificationContract
open scoped BigOperators ComplexOrder Matrix Kronecker

def noisyGeneralTree (γ : Visibility) : ℕ → PairDensity → PairDensity
  | 0, M => M
  | m+1, M => noisyPurified γ (noisyGeneralTree γ m M ⊗ₖ noisyGeneralTree γ m M)

theorem noisyGeneralTree_werner (γ : Visibility) (F : ℝ) (m : ℕ) :
    noisyGeneralTree γ m (werner F) = noisyTreeMatrix γ F m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [noisyGeneralTree, noisyTreeMatrix, ih]

theorem noisyGeneralTree_smul (γ : Visibility) (c : ℂ) (M : PairDensity) (m : ℕ) :
    noisyGeneralTree γ m (c • M) = c^(2^m) • noisyGeneralTree γ m M := by
  induction m with
  | zero => simp [noisyGeneralTree]
  | succ m ih =>
    rw [noisyGeneralTree, ih, Matrix.smul_kronecker, Matrix.kronecker_smul,
      smul_smul, noisyPurified_smul, ← pow_add, pow_succ]
    congr 2
    omega

def noisyRepeaterLevelStep (γ : Visibility) (m : ℕ) (D : PairDensity) : PairDensity :=
  noisyGeneralTree γ m (pairSwap D D)

theorem noisyOrbit_quarter_bounds (γ : Visibility) {F : ℝ}
    (h : 1 / 4 ≤ F ∧ F ≤ 1) (m : ℕ) :
    1 / 4 ≤ noisyOrbit γ.val F m ∧ noisyOrbit γ.val F m ≤ 1 := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [noisyOrbit_succ]
    have hr := recurrence_quarter_bounds ih
    have hlo := mul_nonneg γ.nonnegative (sub_nonneg.mpr hr.1)
    have hhi := mul_nonneg γ.nonnegative (sub_nonneg.mpr hr.2)
    unfold noisyRecurrence
    constructor <;> nlinarith [γ.le_one]

def noisyLevelVisibilityValue (γ : Visibility) (m : ℕ) (w : ℝ) : ℝ :=
  (4 * noisyOrbit γ.val (swapFidelity w) m - 1) / 3

theorem noisyLevelVisibility_bounds (γ : Visibility) (m : ℕ) (w : Visibility) :
    0 ≤ noisyLevelVisibilityValue γ m w.val ∧ noisyLevelVisibilityValue γ m w.val ≤ 1 := by
  have hs : 1 / 4 ≤ swapFidelity w.val ∧ swapFidelity w.val ≤ 1 := by
    have := pow_le_one₀ w.nonnegative w.le_one (n := 2)
    unfold swapFidelity
    constructor <;> nlinarith [sq_nonneg w.val]
  have hf := noisyOrbit_quarter_bounds γ hs m
  unfold noisyLevelVisibilityValue
  constructor <;> linarith

def noisyLevelVisibility (γ : Visibility) (m : ℕ) (w : Visibility) : Visibility :=
  ⟨noisyLevelVisibilityValue γ m w.val, (noisyLevelVisibility_bounds γ m w).1,
    (noisyLevelVisibility_bounds γ m w).2⟩

def noisyLevelProbability (γ : Visibility) (m : ℕ) (w : Visibility) : ℝ :=
  noisyTreeProbability γ.val (swapFidelity w.val) m

theorem noisyLevelProbability_bounds (γ : Visibility) (m : ℕ) (w : Visibility) :
    0 < noisyLevelProbability γ m w ∧ noisyLevelProbability γ m w ≤ 1 := by
  refine ⟨noisyTreeProbability_pos _ _ _, ?_⟩
  have hs : 0 ≤ swapFidelity w.val ∧ swapFidelity w.val ≤ 1 := by
    have := pow_le_one₀ w.nonnegative w.le_one (n := 2)
    unfold swapFidelity
    constructor <;> nlinarith [sq_nonneg w.val]
  exact noisyTreeProbability_le_one γ hs.1 hs.2 m

theorem noisyRepeaterLevelStep_smul (γ : Visibility) (m : ℕ) (c : ℂ) (D : PairDensity) :
    noisyRepeaterLevelStep γ m (c • D) = c^(2^(m+1)) • noisyRepeaterLevelStep γ m D := by
  unfold noisyRepeaterLevelStep
  rw [pairSwap_common_smul, noisyGeneralTree_smul, ← pow_mul]
  congr 2
  simp [pow_succ, Nat.mul_comm]

theorem noisyRepeaterLevelStep_isotropic (γ : Visibility) (m : ℕ) (w : Visibility) :
    noisyRepeaterLevelStep γ m (isotropic w) =
      (noisyLevelProbability γ m w : ℂ) • isotropic (noisyLevelVisibility γ m w) := by
  rw [noisyRepeaterLevelStep, pairSwap_isotropic, isotropic_eq_werner]
  have hs : elemFidelity (multiplyVisibility w w).val = swapFidelity w.val := by
    simp only [elemFidelity, multiplyVisibility, swapFidelity, pow_two]
  rw [hs, noisyGeneralTree_werner, noisyTreeMatrix_eq_werner, isotropic_eq_werner]
  have hf : elemFidelity (noisyLevelVisibility γ m w).val =
      noisyOrbit γ.val (swapFidelity w.val) m := by
    unfold elemFidelity noisyLevelVisibility noisyLevelVisibilityValue
    dsimp
    ring
  rw [hf]
  rfl

/-- Visibility is tracked explicitly; it is never inferred by dividing an arbitrary matrix. -/
structure ScheduledState where
  matrix : PairDensity
  weight : ℝ
  visibility : Visibility

def scheduledStepAcc (γ : Visibility) (a : ScheduledState) (m : ℕ) : ScheduledState :=
  ⟨noisyRepeaterLevelStep γ m a.matrix,
    a.weight^(2^(m+1)) * noisyLevelProbability γ m a.visibility,
    noisyLevelVisibility γ m a.visibility⟩

def scheduledState (γ w : Visibility) (sched : List ℕ) : ScheduledState :=
  sched.foldl (scheduledStepAcc γ) ⟨isotropic w, 1, w⟩

def scheduledRepeaterMatrix (γ w : Visibility) (sched : List ℕ) : PairDensity :=
  (scheduledState γ w sched).matrix

def scheduledRepeaterProbability (γ w : Visibility) (sched : List ℕ) : ℝ :=
  (scheduledState γ w sched).weight

def scheduledVisibility (γ w : Visibility) (sched : List ℕ) : Visibility :=
  (scheduledState γ w sched).visibility

def scheduledVisibilityValue (γ w : Visibility) (sched : List ℕ) : ℝ :=
  (scheduledVisibility γ w sched).val

def scheduledSegmentCount (sched : List ℕ) : ℕ := 2^sched.length

def scheduledRawPairCount (sched : List ℕ) : ℕ :=
  (sched.map (fun m => 2^(m+1))).prod

/-- The invariant binds all three accumulator fields, rather than assuming they agree. -/
def ScheduledState.Valid (a : ScheduledState) : Prop :=
  a.matrix = (a.weight : ℂ) • isotropic a.visibility ∧ 0 < a.weight ∧ a.weight ≤ 1

theorem scheduledStepAcc_valid (γ : Visibility) (a : ScheduledState) (m : ℕ)
    (ha : a.Valid) : (scheduledStepAcc γ a m).Valid := by
  rcases ha with ⟨he, hp, h1⟩
  have hq := noisyLevelProbability_bounds γ m a.visibility
  refine ⟨?_, mul_pos (pow_pos hp _) hq.1, mul_le_one₀ (pow_le_one₀ hp.le h1) hq.1.le hq.2⟩
  change noisyRepeaterLevelStep γ m a.matrix = _
  rw [he, noisyRepeaterLevelStep_smul, noisyRepeaterLevelStep_isotropic, smul_smul]
  simp only [scheduledStepAcc, Complex.ofReal_mul, Complex.ofReal_pow]

theorem scheduledFold_valid (γ : Visibility) (sched : List ℕ) (a : ScheduledState)
    (ha : a.Valid) : (sched.foldl (scheduledStepAcc γ) a).Valid := by
  induction sched generalizing a with
  | nil => exact ha
  | cons m rest ih => exact ih _ (scheduledStepAcc_valid γ a m ha)

theorem scheduledState_valid (γ w : Visibility) (sched : List ℕ) :
    (scheduledState γ w sched).Valid :=
  scheduledFold_valid γ sched _ ⟨by simp, by norm_num, le_rfl⟩

theorem scheduledState_append (γ w : Visibility) (a b : List ℕ) :
    scheduledState γ w (a ++ b) = b.foldl (scheduledStepAcc γ) (scheduledState γ w a) := by
  simp [scheduledState, List.foldl_append]

theorem scheduledState_snoc (γ w : Visibility) (s : List ℕ) (m : ℕ) :
    scheduledState γ w (s ++ [m]) = scheduledStepAcc γ (scheduledState γ w s) m := by
  simp [scheduledState_append]

theorem scheduledRepeaterMatrix_snoc (γ w : Visibility) (s : List ℕ) (m : ℕ) :
    scheduledRepeaterMatrix γ w (s ++ [m]) =
      noisyRepeaterLevelStep γ m (scheduledRepeaterMatrix γ w s) := by
  simp [scheduledRepeaterMatrix, scheduledState_snoc, scheduledStepAcc]

theorem scheduledRepeaterProbability_snoc (γ w : Visibility) (s : List ℕ) (m : ℕ) :
    scheduledRepeaterProbability γ w (s ++ [m]) =
      scheduledRepeaterProbability γ w s ^ (2^(m+1)) *
        noisyLevelProbability γ m (scheduledVisibility γ w s) := by
  simp [scheduledRepeaterProbability, scheduledVisibility, scheduledState_snoc, scheduledStepAcc]

theorem scheduledVisibilityValue_snoc (γ w : Visibility) (s : List ℕ) (m : ℕ) :
    scheduledVisibilityValue γ w (s ++ [m]) =
      noisyLevelVisibilityValue γ m (scheduledVisibilityValue γ w s) := by
  simp [scheduledVisibilityValue, scheduledVisibility, scheduledState_snoc,
    scheduledStepAcc, noisyLevelVisibility]

theorem scheduledRepeaterMatrix_refinement (γ w : Visibility) (s : List ℕ) :
    scheduledRepeaterMatrix γ w s = (scheduledRepeaterProbability γ w s : ℂ) •
      isotropic (scheduledVisibility γ w s) := (scheduledState_valid γ w s).1

theorem scheduledRepeaterProbability_pos (γ w : Visibility) (s : List ℕ) :
    0 < scheduledRepeaterProbability γ w s := (scheduledState_valid γ w s).2.1

theorem scheduledRepeaterProbability_le_one (γ w : Visibility) (s : List ℕ) :
    scheduledRepeaterProbability γ w s ≤ 1 := (scheduledState_valid γ w s).2.2

theorem scheduledRepeaterMatrix_posSemidef (γ w : Visibility) (s : List ℕ) :
    (scheduledRepeaterMatrix γ w s).PosSemidef := by
  rw [scheduledRepeaterMatrix_refinement, Complex.coe_smul]
  exact (density_positive _).smul (scheduledRepeaterProbability_pos γ w s).le

theorem scheduledRepeaterMatrix_trace (γ w : Visibility) (s : List ℕ) :
    (scheduledRepeaterMatrix γ w s).trace = (scheduledRepeaterProbability γ w s : ℂ) := by
  rw [scheduledRepeaterMatrix_refinement, Matrix.trace_smul, isotropic_trace, smul_eq_mul, mul_one]

theorem scheduledRepeaterMatrix_conditional (γ w : Visibility) (s : List ℕ) :
    (scheduledRepeaterProbability γ w s : ℂ)⁻¹ • scheduledRepeaterMatrix γ w s =
      isotropic (scheduledVisibility γ w s) := by
  rw [scheduledRepeaterMatrix_refinement, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (scheduledRepeaterProbability_pos γ w s).ne'),
    one_smul]

theorem scheduledRepeaterMatrix_conditional_density (γ w : Visibility) (s : List ℕ) :
    let D := (scheduledRepeaterProbability γ w s : ℂ)⁻¹ • scheduledRepeaterMatrix γ w s
    D.PosSemidef ∧ D.trace = 1 := by
  dsimp
  rw [scheduledRepeaterMatrix_conditional]
  exact ⟨density_positive _, isotropic_trace _⟩

theorem scheduledRepeaterMatrix_nil (γ w : Visibility) :
    scheduledRepeaterMatrix γ w [] = isotropic w ∧
    scheduledRepeaterProbability γ w [] = 1 ∧
    scheduledSegmentCount [] = 1 ∧ scheduledRawPairCount [] = 1 := by
  simp [scheduledRepeaterMatrix, scheduledRepeaterProbability, scheduledState,
    scheduledSegmentCount, scheduledRawPairCount]

theorem scheduledRawPairCount_append (a b : List ℕ) :
    scheduledRawPairCount (a ++ b) = scheduledRawPairCount a * scheduledRawPairCount b := by
  simp [scheduledRawPairCount, List.prod_append]

theorem scheduledSegmentCount_append (a b : List ℕ) :
    scheduledSegmentCount (a ++ b) = scheduledSegmentCount a * scheduledSegmentCount b := by
  simp [scheduledSegmentCount, pow_add]

theorem noisyRepeaterLevelStep_zero (γ : Visibility) (D : PairDensity) :
    noisyRepeaterLevelStep γ 0 D = pairSwap D D := rfl

theorem noisyLevelVisibilityValue_zero (γ : Visibility) (w : ℝ) :
    noisyLevelVisibilityValue γ 0 w = w^2 := by
  simp only [noisyLevelVisibilityValue, noisyOrbit_zero, swapFidelity]
  ring

theorem scheduled_zero_depths (γ w : Visibility) (k : ℕ) :
    scheduledVisibilityValue γ w (List.replicate k 0) = w.val^(2^k) ∧
    scheduledRepeaterProbability γ w (List.replicate k 0) = 1 ∧
    scheduledRawPairCount (List.replicate k 0) = 2^k := by
  induction k with
  | zero => simp [scheduledVisibilityValue, scheduledVisibility, scheduledState,
      scheduledRepeaterProbability, scheduledRawPairCount]
  | succ k ih =>
    rw [List.replicate_succ', scheduledVisibilityValue_snoc,
      noisyLevelVisibilityValue_zero, ih.1, ← pow_mul]
    constructor
    · rw [pow_succ]
    constructor
    · rw [scheduledRepeaterProbability_snoc, ih.2.1]
      simp [noisyLevelProbability, noisyTreeProbability]
    · rw [scheduledRawPairCount_append, ih.2.2]
      simp [scheduledRawPairCount, pow_succ]

theorem noisyGeneralTree_unit (m : ℕ) (M : PairDensity) :
    noisyGeneralTree unitVisibility m M = purifiedTree m M := by
  have hunit (A : FourDensity) : noisyPurified unitVisibility A = purified A := by
    rw [noisyPurified, depolarizing_map]
    simp [unitVisibility]
  induction m with
  | zero => rfl
  | succ m ih => simp only [noisyGeneralTree, purifiedTree, ih, hunit]

theorem scheduledRepeaterMatrix_ideal_replicate (w : Visibility) (k m : ℕ) :
    scheduledRepeaterMatrix unitVisibility w (List.replicate k m) =
      nestedRepeaterMatrix m w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', scheduledRepeaterMatrix_snoc, ih]
    exact noisyGeneralTree_unit m _

/-- Scalar degree of the actual matrix composition equals the raw resource count. -/
theorem scheduledFold_matrix_smul (γ : Visibility) (s : List ℕ)
    (a b : ScheduledState) (c : ℂ) (h : b.matrix = c • a.matrix) :
    (s.foldl (scheduledStepAcc γ) b).matrix =
      c^(scheduledRawPairCount s) • (s.foldl (scheduledStepAcc γ) a).matrix := by
  induction s generalizing a b c with
  | nil => simpa [scheduledRawPairCount] using h
  | cons m rest ih =>
    have hs : (scheduledStepAcc γ b m).matrix =
        c^(2^(m+1)) • (scheduledStepAcc γ a m).matrix := by
      change noisyRepeaterLevelStep γ m b.matrix = _
      rw [h, noisyRepeaterLevelStep_smul]
      rfl
    have hi := ih _ _ _ hs
    rw [← pow_mul] at hi
    simpa [scheduledRawPairCount] using hi

theorem scheduledRawPairCount_replicate (k m : ℕ) :
    scheduledRawPairCount (List.replicate k m) = 2^((m+1)*k) := by
  induction k with
  | zero => simp [scheduledRawPairCount]
  | succ k ih =>
    rw [List.replicate_succ', scheduledRawPairCount_append, ih]
    simp [scheduledRawPairCount, Nat.mul_add, pow_add]

theorem scheduledVisibilityValue_bounds (γ w : Visibility) (s : List ℕ) :
    0 ≤ scheduledVisibilityValue γ w s ∧ scheduledVisibilityValue γ w s ≤ 1 :=
  ⟨(scheduledVisibility γ w s).nonnegative, (scheduledVisibility γ w s).le_one⟩

/-- Local conditions are imposed only on actual chronological steps of the schedule. -/
def LocalQualityGain (γ w : Visibility) (s : List ℕ) : Prop :=
  ∀ pref m suffix, s = pref ++ m :: suffix →
    scheduledVisibilityValue γ w pref ≤
      noisyLevelVisibilityValue γ m (scheduledVisibilityValue γ w pref)

theorem scheduledVisibility_prefix_sustains_initial_of_local_gain
    (γ w : Visibility) (s : List ℕ) (hg : LocalQualityGain γ w s)
    (pref : List ℕ) (hp : pref <+: s) :
    w.val ≤ scheduledVisibilityValue γ w pref := by
  induction pref using List.reverseRecOn with
  | nil => exact le_rfl
  | append_singleton pref m ih =>
    obtain ⟨suffix, he⟩ := hp
    have he' : s = pref ++ m :: suffix := by simpa [List.append_assoc] using he.symm
    have hp' : pref <+: s := ⟨m :: suffix, he'.symm⟩
    rw [scheduledVisibilityValue_snoc]
    exact le_trans (ih hp') (hg pref m suffix he')

theorem scheduledVisibility_sustains_initial_of_local_gain
    (γ w : Visibility) (s : List ℕ) (hg : LocalQualityGain γ w s) :
    w.val ≤ scheduledVisibilityValue γ w s :=
  scheduledVisibility_prefix_sustains_initial_of_local_gain γ w s hg s ⟨[], by simp⟩

structure QuantumScheduledNoisyRepeaterSuite : Prop where
  refinement : ∀ γ w s, scheduledRepeaterMatrix γ w s =
    (scheduledRepeaterProbability γ w s : ℂ) • isotropic (scheduledVisibility γ w s)
  probability : ∀ γ w s, 0 < scheduledRepeaterProbability γ w s ∧
    scheduledRepeaterProbability γ w s ≤ 1
  quality : ∀ γ w s, LocalQualityGain γ w s → w.val ≤ scheduledVisibilityValue γ w s

theorem verification_suite : QuantumScheduledNoisyRepeaterSuite :=
  ⟨scheduledRepeaterMatrix_refinement,
    fun γ w s => ⟨scheduledRepeaterProbability_pos γ w s,
      scheduledRepeaterProbability_le_one γ w s⟩,
    scheduledVisibility_sustains_initial_of_local_gain⟩

end QuantumScheduledNoisyRepeater

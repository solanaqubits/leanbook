/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite receiver counterexample and linearized observation algebra.
No nonlinear inverse theorem, neutrino Hamiltonian refinement or numerical-rank
certificate is claimed. A Fisher/Gram condition is a first-order condition. -/
namespace PrometheusThresholdTomography
noncomputable section
open scoped BigOperators Matrix

/-- Joint probabilities; zero-mass terms contribute zero. -/
def mutualInformation {n m : ℕ} (p : Fin n → Fin m → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * Real.log (p x y / ((∑ z, p x z) * (∑ z, p z y))) / Real.log 2

/-- Threshold kernel and prior can depend on the modeled receiver state. This
normalization theorem assumes the supplied kernel is a conditional distribution. -/
def jointFromKernel {m : ℕ} (prior : Fin 2 → ℝ) (kernel : Fin 2 → Fin m → ℝ) :=
  fun x y => prior x * kernel x y

theorem joint_normalized {m : ℕ} (prior : Fin 2 → ℝ) (kernel : Fin 2 → Fin m → ℝ)
    (hp : ∑ x, prior x = 1) (hk : ∀ x, ∑ y, kernel x y = 1) :
    ∑ x, ∑ y, jointFromKernel prior kernel x y = 1 := by
  simp only [jointFromKernel, ← Finset.mul_sum, hk, mul_one]
  exact hp

def trigger (ac rf relative halfWidth ta tr : ℝ) (ready : Bool) : Prop :=
  ready = true ∧ ta ≤ ac ∧ tr ≤ rf ∧ |relative| ≤ halfWidth

theorem dead_time_blocks (ac rf delta w ta tr : ℝ) : ¬ trigger ac rf delta w ta tr false := by
  simp [trigger]

def profile {j : ℕ} (baseline : ℝ → ℝ) (basis : Fin j → ℝ → ℝ)
    (a : Fin j → ℝ) (r : ℝ) : ℝ := baseline r + ∑ i, a i * basis i r

/-- Balanced noiseless binary input: observations 0,1,erasure. Both amplitudes
are exactly one. Fix radio threshold at zero and vary acoustic threshold. -/
def atomicJoint (threshold : ℝ) (x : Fin 2) (y : Fin 3) : ℝ :=
  if threshold ≤ 1 then (if y.val = x.val then 1/2 else 0)
  else (if y.val = 2 then 1/2 else 0)

theorem atomic_nonnegative (t : ℝ) (x : Fin 2) (y : Fin 3) : 0 ≤ atomicJoint t x y := by
  unfold atomicJoint
  split_ifs <;> norm_num

theorem atomic_normalized (t : ℝ) : ∑ x, ∑ y, atomicJoint t x y = 1 := by
  by_cases h : t ≤ 1 <;> norm_num [atomicJoint, h, Fin.sum_univ_succ]

theorem atomic_information (t : ℝ) :
    mutualInformation (atomicJoint t) = if t ≤ 1 then 1 else 0 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  by_cases h : t ≤ 1 <;> norm_num [mutualInformation, atomicJoint, h, Fin.sum_univ_succ, hlog]

/-- Negative semidefinite Hessians concern concavity, not convexity. Atomic
threshold objectives need not even be smooth. This is a genuine MI counterexample. -/
theorem atomic_not_concave :
    ¬ ConcaveOn ℝ Set.univ (fun t => mutualInformation (atomicJoint t)) := by
  rintro ⟨_, h⟩
  have hs := h (x := 0) (Set.mem_univ _) (y := 3) (Set.mem_univ _)
    (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [atomic_information] at hs

theorem atomic_not_convex :
    ¬ ConvexOn ℝ Set.univ (fun t => mutualInformation (atomicJoint t)) := by
  rintro ⟨_, h⟩
  have hs := h (x := 0) (Set.mem_univ _) (y := 2) (Set.mem_univ _)
    (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [atomic_information] at hs

/-- No test distribution appears in this finite training-set optimality claim. -/
theorem grid_max_only {α : Type*} (score : α → ℝ) (grid : Finset α) (chosen : α)
    (selection : ∀ x ∈ grid, score x ≤ score chosen) (x : α) (hx : x ∈ grid) :
    score x ≤ score chosen := selection x hx

/-- First-order sensitivity after any explicitly chosen calibration/whitening. -/
def identifiable {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ) : Prop :=
  Function.Injective A.mulVec

def gram {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ) := A.transpose * A

theorem gram_rank {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ) :
    (gram A).rank = A.rank := Matrix.rank_transpose_mul_self A

theorem gram_kernel {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ) :
    LinearMap.ker (gram A).mulVecLin = LinearMap.ker A.mulVecLin :=
  Matrix.ker_mulVecLin_transpose_mul_self A

theorem identifiable_iff_gram_kernel {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ) :
    identifiable A ↔ LinearMap.ker (gram A).mulVecLin = ⊥ := by
  rw [gram_kernel, LinearMap.ker_eq_bot]
  rfl

theorem identifiable_iff_columns {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ) :
    identifiable A ↔ LinearIndependent ℝ A.col := Matrix.mulVec_injective_iff

theorem linearized_unique {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ)
    (h : identifiable A) (a b : Fin j → ℝ) (same : A *ᵥ a = A *ᵥ b) : a = b := h same

/-- Arbitrarily many distinct energies may still have identical parameter columns. -/
def duplicateColumns {k : ℕ} (response : Fin k → ℝ) : Matrix (Fin k) (Fin 2) ℝ :=
  fun i _ => response i

def hiddenDirection : Fin 2 → ℝ := ![1, -1]

theorem hidden_nonzero : hiddenDirection ≠ 0 := by
  intro h
  have := congrFun h 0
  norm_num [hiddenDirection] at this

theorem duplicate_kernel {k : ℕ} (response : Fin k → ℝ) :
    duplicateColumns response *ᵥ hiddenDirection = 0 := by
  ext i
  simp [Matrix.mulVec, dotProduct, duplicateColumns, hiddenDirection, Fin.sum_univ_succ]

theorem multienergy_not_sufficient {k : ℕ} (response : Fin k → ℝ) :
    ¬ identifiable (duplicateColumns response) := by
  intro h
  have same : duplicateColumns response *ᵥ hiddenDirection = duplicateColumns response *ᵥ 0 := by
    rw [duplicate_kernel, Matrix.mulVec_zero]
  exact hidden_nonzero (h same)

theorem duplicate_rank_lt_two {k : ℕ} (response : Fin k → ℝ) :
    (duplicateColumns response).rank < 2 := by
  let L : Matrix (Fin k) (Fin 1) ℝ := fun i _ => response i
  let R : Matrix (Fin 1) (Fin 2) ℝ := fun _ _ => 1
  have heq : duplicateColumns response = L * R := by
    ext i j
    change response i = ∑ l : Fin 1, L i l * R l j
    simp [L, R]
  rw [heq]
  have h := (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_card_width L)
  norm_num at h
  omega

/-- Exact source-flux / efficiency confounding in count means. -/
def countMean (flux efficiency probability background : ℝ) : ℝ :=
  flux * efficiency * probability + background

theorem flux_efficiency_gauge (f e p b c : ℝ) (hc : c ≠ 0) :
    countMean (f*c) (e/c) p b = countMean f e p b := by
  unfold countMean
  field_simp

/-- More columns than observations cannot have full rank. -/
theorem insufficient_observations {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ) (h : k < j) :
    A.rank < j := lt_of_le_of_lt (by simpa using Matrix.rank_le_card_height A) h

structure PrometheusThresholdTomographySuite : Prop where
  not_concave : ¬ ConcaveOn ℝ Set.univ (fun t => mutualInformation (atomicJoint t))
  not_convex : ¬ ConvexOn ℝ Set.univ (fun t => mutualInformation (atomicJoint t))
  gram_preserves_rank : ∀ {k j : ℕ} (A : Matrix (Fin k) (Fin j) ℝ), (gram A).rank = A.rank
  energy_insufficient : ∀ {k : ℕ} (r : Fin k → ℝ), ¬ identifiable (duplicateColumns r)

theorem verification_suite : PrometheusThresholdTomographySuite :=
  ⟨atomic_not_concave, atomic_not_convex, gram_rank, multienergy_not_sufficient⟩
end
end PrometheusThresholdTomography

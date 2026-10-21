/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaComparisonContract

/-! Fast absorbed and zero-window branches. Equality holds for every rational
profile. Counts are source-level operations; control guards, allocation, bit
costs and machine time are excluded. Existing selectors and counters are unchanged. -/
namespace CryptoHiddenScalarQuotaFastContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaBudgetContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarQuotaCostContract
open CryptoHiddenScalarQuotaComparisonContract

/-- Guards precede all row construction. A negative tolerance is not globally
rejected: outside probability ranges a nonabsorbed deficit may be negative. -/
def chooseQuotaBudgetFastWithin (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) : Option ℕ :=
  if n ≤ j then
    if 0 ≤ ε then some 0 else none
  else if cap = 0 then
    if 1 ≤ ε then some 0 else none
  else chooseQuotaBudgetStreamingWithin n p j ε cap

theorem chooseQuotaBudgetWithin_zero_cap (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (hj : j < n) :
    chooseQuotaBudgetWithin n p j ε 0 = if 1 ≤ ε then some 0 else none := by
  simp [chooseQuotaBudgetWithin, searchThrough, quotaDeficit, quotaLower,
    Nat.not_le.mpr hj]

theorem chooseQuotaBudgetFastWithin_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) :
    chooseQuotaBudgetFastWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap := by
  by_cases hj : n ≤ j
  · by_cases he : 0 ≤ ε
    · simpa [chooseQuotaBudgetFastWithin, hj, he] using
        (chooseQuotaBudgetWithin_absorbed n p j ε cap hj he).symm
    · simpa [chooseQuotaBudgetFastWithin, hj, he] using
        (chooseQuotaBudgetWithin_absorbed_negative n p j ε cap hj
          (lt_of_not_ge he)).symm
  · by_cases hc : cap = 0
    · subst cap
      simpa [chooseQuotaBudgetFastWithin, hj] using
        (chooseQuotaBudgetWithin_zero_cap n p j ε (by omega)).symm
    · simpa [chooseQuotaBudgetFastWithin, hj, hc] using
        chooseQuotaBudgetStreamingWithin_eq n p j ε cap

/-- One deficit comparison in either fast branch. The regular branch invokes
exactly one old instrumented search and adds its explicit initial-row count.
Natural-number control guards are excluded from the deficit-check counter. -/
def chooseQuotaBudgetFastInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) : Option ℕ × TabularStats :=
  if n ≤ j then
    (if 0 ≤ ε then some 0 else none, ⟨1, 0, 0, 0⟩)
  else if cap = 0 then
    (if 1 ≤ ε then some 0 else none, ⟨1, 0, 0, 0⟩)
  else
    let result := chooseQuotaBudgetInstrumented n p j ε cap
    (result.1, ⟨result.2.checks, 1, result.2.transitions, result.2.updates⟩)

theorem chooseQuotaBudgetFastInstrumented_result (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetFastInstrumented n p j ε cap).1 =
      chooseQuotaBudgetFastWithin n p j ε cap := by
  simp only [chooseQuotaBudgetFastInstrumented, chooseQuotaBudgetFastWithin]
  split_ifs <;> simp [chooseQuotaBudgetInstrumented_eq_streaming]

theorem chooseQuotaBudgetFastInstrumented_fast_stats (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) (h : n ≤ j ∨ cap = 0) :
    (chooseQuotaBudgetFastInstrumented n p j ε cap).2 = ⟨1, 0, 0, 0⟩ := by
  unfold chooseQuotaBudgetFastInstrumented
  split_ifs <;> simp_all

theorem chooseQuotaBudgetFastInstrumented_regular_stats (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) (hj : j < n) (hc : 0 < cap) :
    (chooseQuotaBudgetFastInstrumented n p j ε cap).2 = streamingStats n p j ε cap := by
  simp [chooseQuotaBudgetFastInstrumented, Nat.not_le.mpr hj, Nat.ne_of_gt hc,
    streamingStats]

/-- Complete branch-sensitive closed form, derived from the existing counters. -/
theorem chooseQuotaBudgetFastInstrumented_stats (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) :
    let t := lastBudget (chooseQuotaBudgetFastWithin n p j ε cap) cap
    (chooseQuotaBudgetFastInstrumented n p j ε cap).2 =
      if n ≤ j ∨ cap = 0 then ⟨1, 0, 0, 0⟩ else ⟨t+1, 1, t, n*t⟩ := by
  dsimp only
  split_ifs with h
  · exact chooseQuotaBudgetFastInstrumented_fast_stats n p j ε cap h
  · rw [chooseQuotaBudgetFastInstrumented_regular_stats n p j ε cap (by omega) (by omega)]
    rw [streaming_stats, chooseQuotaBudgetTabularInstrumented_eq,
      CryptoHiddenScalarQuotaTabularContract.chooseQuotaBudgetTabularWithin_eq,
      chooseQuotaBudgetFastWithin_eq]

/-- Stability of an already selected budget under a larger search window.
This does not assert monotonicity of the rational deficit in its budget. -/
theorem chooseQuotaBudgetFastWithin_extend_some (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap₁ cap₂ t : ℕ) (hc : cap₁ ≤ cap₂)
    (hs : chooseQuotaBudgetFastWithin n p j ε cap₁ = some t) :
    chooseQuotaBudgetFastWithin n p j ε cap₂ = some t := by
  rw [chooseQuotaBudgetFastWithin_eq] at hs ⊢
  have ht := chooseQuotaBudgetWithin_sound n p j ε cap₁ t hs
  cases hh : chooseQuotaBudgetWithin n p j ε cap₂ with
  | none =>
    exact False.elim (not_lt_of_ge ht.2
      ((chooseQuotaBudgetWithin_none_iff n p j ε cap₂).mp hh t (by omega)))
  | some k =>
    have hk := chooseQuotaBudgetWithin_sound n p j ε cap₂ k hh
    have hmin := chooseQuotaBudgetWithin_minimal n p j ε cap₁ t hs
    have hmin' := chooseQuotaBudgetWithin_minimal n p j ε cap₂ k hh
    have he : k = t := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact not_lt_of_ge hk.2 (hmin k hlt)
      · exact not_lt_of_ge ht.2 (hmin' t hgt)
    simp [he]

/-- Failure remains a statement about the supplied finite window only. -/
theorem chooseQuotaBudgetFastWithin_none_iff (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) :
    chooseQuotaBudgetFastWithin n p j ε cap = none ↔
      ∀ t ≤ cap, ε < quotaDeficit n p t j := by
  rw [chooseQuotaBudgetFastWithin_eq, chooseQuotaBudgetWithin_none_iff]

structure CryptoHiddenScalarQuotaFastContractSuite : Prop where
  search : ∀ n p j ε cap,
    chooseQuotaBudgetFastWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap
  instrumented : ∀ n p j ε cap, (chooseQuotaBudgetFastInstrumented n p j ε cap).1 =
    chooseQuotaBudgetFastWithin n p j ε cap
  fast_stats : ∀ n p j ε cap, n ≤ j ∨ cap = 0 →
    (chooseQuotaBudgetFastInstrumented n p j ε cap).2 = ⟨1, 0, 0, 0⟩
  regular_stats : ∀ n p j ε cap, j < n → 0 < cap →
    (chooseQuotaBudgetFastInstrumented n p j ε cap).2 = streamingStats n p j ε cap
  extension : ∀ n p j ε cap₁ cap₂ t, cap₁ ≤ cap₂ →
    chooseQuotaBudgetFastWithin n p j ε cap₁ = some t →
    chooseQuotaBudgetFastWithin n p j ε cap₂ = some t
  window : ∀ n p j ε cap, chooseQuotaBudgetFastWithin n p j ε cap = none ↔
    ∀ t ≤ cap, ε < quotaDeficit n p t j

theorem verification_suite : CryptoHiddenScalarQuotaFastContractSuite where
  search := chooseQuotaBudgetFastWithin_eq
  instrumented := chooseQuotaBudgetFastInstrumented_result
  fast_stats := chooseQuotaBudgetFastInstrumented_fast_stats
  regular_stats := chooseQuotaBudgetFastInstrumented_regular_stats
  extension := chooseQuotaBudgetFastWithin_extend_some
  window := chooseQuotaBudgetFastWithin_none_iff
end CryptoHiddenScalarQuotaFastContract

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaResumeCostContract

/-! Fast successful starts preserve the entire resumable result. A failed outer
threshold test is counted in addition to the delegated start's repeated test.
Natural control guards, runtime packaging and machine allocations are excluded. -/
namespace CryptoHiddenScalarQuotaFastStartContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaResumeCostContract

/-- Only successful zero-budget branches avoid initial row construction.
Failure delegates unchanged, including its exact exhausted row. -/
def startQuotaSearchFast (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    QuotaSearchResult n p j ε :=
  if n ≤ j then
    if 0 ≤ ε then .found 0 else startQuotaSearch n p j ε cap
  else
    if 1 ≤ ε then .found 0 else startQuotaSearch n p j ε cap

/-- A zero-budget success determines the full result, not merely its projection. -/
theorem start_found_zero (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (h : quotaDeficit n p 0 j ≤ ε) : startQuotaSearch n p j ε cap = .found 0 := by
  have hm : IsMinimalQuotaBudget n p j ε 0 := ⟨h, by intro t ht; omega⟩
  have hs := (startQuotaSearch_eq n p j ε cap).trans
    (minimal_selected n p j ε 0 cap hm (Nat.zero_le _))
  cases he : startQuotaSearch n p j ε cap <;>
    simp_all [QuotaSearchResult.toOption]

theorem start_found_zero_absorbed (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (hj : n ≤ j) (he : 0 ≤ ε) : startQuotaSearch n p j ε cap = .found 0 := by
  apply start_found_zero
  simpa [quotaDeficit, quotaLower, hj] using he

theorem start_found_zero_unabsorbed (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (hj : j < n) (he : 1 ≤ ε) : startQuotaSearch n p j ε cap = .found 0 := by
  apply start_found_zero
  simpa [quotaDeficit, quotaLower, Nat.not_le.mpr hj] using he

/-- Unconditional equality includes cursor bound, row and Prop certificates. -/
theorem startQuotaSearchFast_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    startQuotaSearchFast n p j ε cap = startQuotaSearch n p j ε cap := by
  unfold startQuotaSearchFast
  split_ifs with hj he he
  · exact (start_found_zero_absorbed n p j ε cap hj he).symm
  · rfl
  · exact (start_found_zero_unabsorbed n p j ε cap (by omega) he).symm
  · rfl

theorem startQuotaSearchFast_toOption (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (startQuotaSearchFast n p j ε cap).toOption = chooseQuotaBudgetWithin n p j ε cap := by
  rw [startQuotaSearchFast_eq, startQuotaSearch_eq]

/-- Counters follow executed branches. Delegation adds one failed rational
threshold comparison, even though budget zero is checked again by the old start. -/
def startQuotaSearchFastInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    QuotaSearchResult n p j ε × TabularStats :=
  if n ≤ j then
    if 0 ≤ ε then (.found 0, ⟨1, 0, 0, 0⟩)
    else
      let r := startQuotaSearchInstrumented n p j ε cap
      (r.1, { r.2 with checks := r.2.checks + 1 })
  else
    if 1 ≤ ε then (.found 0, ⟨1, 0, 0, 0⟩)
    else
      let r := startQuotaSearchInstrumented n p j ε cap
      (r.1, { r.2 with checks := r.2.checks + 1 })

theorem startQuotaSearchFastInstrumented_result (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) :
    (startQuotaSearchFastInstrumented n p j ε cap).1 =
      startQuotaSearchFast n p j ε cap := by
  unfold startQuotaSearchFastInstrumented startQuotaSearchFast
  split_ifs <;> simp [start_result]

theorem fast_success (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (h : (n ≤ j ∧ 0 ≤ ε) ∨ (j < n ∧ 1 ≤ ε)) :
    startQuotaSearchFastInstrumented n p j ε cap = (.found 0, ⟨1, 0, 0, 0⟩) := by
  rcases h with ⟨hj, he⟩ | ⟨hj, he⟩
  · simp [startQuotaSearchFastInstrumented, hj, he]
  · simp [startQuotaSearchFastInstrumented, Nat.not_le.mpr hj, he]

/-- The complete fallback pair, including the one extra check. -/
theorem fast_delegates (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (h : (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1)) :
    startQuotaSearchFastInstrumented n p j ε cap =
      let r := startQuotaSearchInstrumented n p j ε cap
      (r.1, { r.2 with checks := r.2.checks + 1 }) := by
  rcases h with ⟨hj, he⟩ | ⟨hj, he⟩
  · simp [startQuotaSearchFastInstrumented, hj, not_le.mpr he]
  · simp [startQuotaSearchFastInstrumented, Nat.not_le.mpr hj, not_le.mpr he]

theorem fast_delegated_counts (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (h : (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1)) :
    let t := (startQuotaSearch n p j ε cap).toOption.getD cap
    (startQuotaSearchFastInstrumented n p j ε cap).2 = ⟨t + 2, 1, t, n * t⟩ := by
  rw [fast_delegates n p j ε cap h]
  have hs := start_counts n p j ε cap
  rw [start_result] at hs
  simp [hs, Nat.add_assoc]

/-- This statement concerns the same retained cursor, with no recomputation claim. -/
theorem fast_exhausted_bound (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (c : QuotaSearchCursor n p j ε) (h : startQuotaSearchFast n p j ε cap = .exhausted c) :
    c.bound = cap := by
  rw [startQuotaSearchFast_eq] at h
  exact startQuotaSearch_bound n p j ε cap c h

structure CryptoHiddenScalarQuotaFastStartContractSuite : Prop where
  result : ∀ n p j ε cap, startQuotaSearchFast n p j ε cap = startQuotaSearch n p j ε cap
  instrumented : ∀ n p j ε cap,
    (startQuotaSearchFastInstrumented n p j ε cap).1 = startQuotaSearchFast n p j ε cap
  success : ∀ n p j ε cap, (n ≤ j ∧ 0 ≤ ε) ∨ (j < n ∧ 1 ≤ ε) →
    startQuotaSearchFastInstrumented n p j ε cap = (.found 0, ⟨1, 0, 0, 0⟩)
  fallback : ∀ n p j ε cap, (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1) →
    (startQuotaSearchFastInstrumented n p j ε cap).2 =
      let t := (startQuotaSearch n p j ε cap).toOption.getD cap
      ⟨t + 2, 1, t, n * t⟩

theorem verification_suite : CryptoHiddenScalarQuotaFastStartContractSuite where
  result := startQuotaSearchFast_eq
  instrumented := startQuotaSearchFastInstrumented_result
  success := fast_success
  fallback := fast_delegated_counts
end CryptoHiddenScalarQuotaFastStartContract

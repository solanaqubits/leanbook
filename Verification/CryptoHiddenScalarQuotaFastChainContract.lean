/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaChainContract
import Verification.CryptoHiddenScalarQuotaFastStartContract

/-! Actual resume chains with one fast start. Structural counts exclude natural
control guards, packaging, stack, machine allocations and rational bit costs. -/
namespace CryptoHiddenScalarQuotaFastChainContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaChainContract
open CryptoHiddenScalarQuotaFastStartContract

/-- Execute the existing continuation fold from the actual fast-start pair. -/
def runQuotaResumeChainFastInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) : QuotaSearchResult n p j ε × TabularStats :=
  quotaResumeChainFold (startQuotaSearchFastInstrumented n p j ε cap₀) caps

/-- One preexisting extra check is carried through the fold, not added per step. -/
theorem fold_extra_check {n p j ε} (r : QuotaSearchResult n p j ε)
    (s : TabularStats) (caps : List ℕ) :
    quotaResumeChainFold (r, {s with checks := s.checks + 1}) caps =
      let out := quotaResumeChainFold (r, s) caps
      (out.1, {out.2 with checks := out.2.checks + 1}) := by
  induction caps generalizing r s with
  | nil => rfl
  | cons c cs ih =>
    simp only [quotaResumeChainFold, quotaResumeChainStep]
    have h : ({s with checks := s.checks + 1}).add
        (resumeQuotaSearchInstrumented r c).2 =
        {s.add (resumeQuotaSearchInstrumented r c).2 with
          checks := (s.add (resumeQuotaSearchInstrumented r c).2).checks + 1} := by
      simp [TabularStats.add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [h]
    exact ih _ _

/-- Terminal success keeps all accumulated counts, even on a nonmonotone tail. -/
theorem fold_found {n p j ε} (T : ℕ) (s : TabularStats) (caps : List ℕ) :
    quotaResumeChainFold ((.found T : QuotaSearchResult n p j ε), s) caps =
      (.found T, s) := by
  induction caps with
  | nil => rfl
  | cons c cs ih =>
    simpa [quotaResumeChainFold, quotaResumeChainStep,
      resumeQuotaSearchInstrumented, TabularStats.add] using ih

/-- Fast success is independent of the tail's bounds or length. -/
theorem fast_chain_success (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ)
    (h : (n ≤ j ∧ 0 ≤ ε) ∨ (j < n ∧ 1 ≤ ε)) :
    runQuotaResumeChainFastInstrumented n p j ε cap₀ caps = (.found 0, ⟨1, 0, 0, 0⟩) := by
  rw [runQuotaResumeChainFastInstrumented, fast_success n p j ε cap₀ h, fold_found]

/-- For any tail, delegation differs from the old executed chain by one check. -/
theorem fast_chain_delegates (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ)
    (h : (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1)) :
    runQuotaResumeChainFastInstrumented n p j ε cap₀ caps =
      let out := runQuotaResumeChainInstrumented n p j ε cap₀ caps
      (out.1, {out.2 with checks := out.2.checks + 1}) := by
  rw [runQuotaResumeChainFastInstrumented, fast_delegates n p j ε cap₀ h]
  exact fold_extra_check _ _ caps

/-- The single pair invariant: a monotone chain equals one cold fast start. -/
theorem fast_chain_pair_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    runQuotaResumeChainFastInstrumented n p j ε cap₀ caps =
      startQuotaSearchFastInstrumented n p j ε (lastCap cap₀ caps) := by
  by_cases hs : (n ≤ j ∧ 0 ≤ ε) ∨ (j < n ∧ 1 ≤ ε)
  · rw [fast_chain_success n p j ε cap₀ caps hs,
      fast_success n p j ε (lastCap cap₀ caps) hs]
  · have hf : (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1) := by
      by_cases hj : n ≤ j
      · exact Or.inl ⟨hj, lt_of_not_ge (fun he => hs (Or.inl ⟨hj, he⟩))⟩
      · exact Or.inr ⟨by omega, lt_of_not_ge (fun he => hs (Or.inr ⟨by omega, he⟩))⟩
    rw [fast_chain_delegates n p j ε cap₀ caps hf, chain_pair_eq n p j ε cap₀ caps hc,
      fast_delegates n p j ε (lastCap cap₀ caps) hf]
    simp only [start_result, start_cold_stats]

/-- Full retained state, including the exhausted bound and row. -/
theorem fast_chain_result (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    (runQuotaResumeChainFastInstrumented n p j ε cap₀ caps).1 =
      startQuotaSearch n p j ε (lastCap cap₀ caps) := by
  rw [fast_chain_pair_eq n p j ε cap₀ caps hc,
    startQuotaSearchFastInstrumented_result, startQuotaSearchFast_eq]

theorem fast_chain_toOption (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    (runQuotaResumeChainFastInstrumented n p j ε cap₀ caps).1.toOption =
      chooseQuotaBudgetWithin n p j ε (lastCap cap₀ caps) := by
  rw [fast_chain_result n p j ε cap₀ caps hc, startQuotaSearch_eq]

/-- In fallback, the only difference from cold streaming is one initial check. -/
theorem fast_chain_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps))
    (hf : (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1)) :
    (runQuotaResumeChainFastInstrumented n p j ε cap₀ caps).2 =
      let s := streamingStats n p j ε (lastCap cap₀ caps)
      {s with checks := s.checks + 1} := by
  rw [fast_chain_delegates n p j ε cap₀ caps hf, chain_pair_eq n p j ε cap₀ caps hc]

theorem fast_chain_counts (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps))
    (hf : (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1)) :
    let cap := lastCap cap₀ caps
    let t := (chooseQuotaBudgetWithin n p j ε cap).getD cap
    (runQuotaResumeChainFastInstrumented n p j ε cap₀ caps).2 = ⟨t + 2, 1, t, n * t⟩ := by
  rw [fast_chain_stats n p j ε cap₀ caps hc hf, cold_counts]

theorem fast_chain_exhausted_bound (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps))
    (c : QuotaSearchCursor n p j ε)
    (h : (runQuotaResumeChainFastInstrumented n p j ε cap₀ caps).1 = .exhausted c) :
    c.bound = lastCap cap₀ caps := by
  rw [fast_chain_result n p j ε cap₀ caps hc] at h
  exact startQuotaSearch_bound n p j ε _ c h

structure CryptoHiddenScalarQuotaFastChainContractSuite : Prop where
  pair : ∀ n p j ε cap₀ caps, List.IsChain (· ≤ ·) (cap₀ :: caps) →
    runQuotaResumeChainFastInstrumented n p j ε cap₀ caps =
      startQuotaSearchFastInstrumented n p j ε (lastCap cap₀ caps)
  result : ∀ n p j ε cap₀ caps, List.IsChain (· ≤ ·) (cap₀ :: caps) →
    (runQuotaResumeChainFastInstrumented n p j ε cap₀ caps).1 =
      startQuotaSearch n p j ε (lastCap cap₀ caps)
  success : ∀ n p j ε cap₀ caps, (n ≤ j ∧ 0 ≤ ε) ∨ (j < n ∧ 1 ≤ ε) →
    runQuotaResumeChainFastInstrumented n p j ε cap₀ caps = (.found 0, ⟨1, 0, 0, 0⟩)
  fallback : ∀ n p j ε cap₀ caps, List.IsChain (· ≤ ·) (cap₀ :: caps) →
    (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1) →
    (runQuotaResumeChainFastInstrumented n p j ε cap₀ caps).2 =
      let cap := lastCap cap₀ caps
      let t := (chooseQuotaBudgetWithin n p j ε cap).getD cap
      ⟨t + 2, 1, t, n * t⟩

theorem verification_suite : CryptoHiddenScalarQuotaFastChainContractSuite where
  pair := fast_chain_pair_eq
  result := fast_chain_result
  success := fast_chain_success
  fallback := fast_chain_counts
end CryptoHiddenScalarQuotaFastChainContract

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaResumeCostContract

/-! Finite chains of actual resumptions. Equality includes retained cursors and
all four structural counters. No machine-cost or probability-range assumptions. -/
namespace CryptoHiddenScalarQuotaChainContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaMinimumContract

/-- The row and proof fields are uniquely fixed by the bound. -/
theorem cursor_ext {n p j ε} (c d : QuotaSearchCursor n p j ε)
    (h : c.bound = d.bound) : c = d := by
  rcases c with ⟨b, r, hr, hp⟩
  rcases d with ⟨b', r', hr', hp'⟩
  dsimp only at h
  subst b'
  cases hr
  cases hr'
  rfl

/-- Full result equality, strengthening the earlier Option-only bridge. -/
theorem resumeQuotaSearch_startQuotaSearch (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (a b : ℕ) (hab : a ≤ b) :
    resumeQuotaSearch (startQuotaSearch n p j ε a) b = startQuotaSearch n p j ε b := by
  have ho := (resume_start_eq n p j ε a b hab).trans (startQuotaSearch_eq n p j ε b).symm
  cases ha : startQuotaSearch n p j ε a with
  | found t =>
    cases hb : startQuotaSearch n p j ε b with
    | found u =>
      simp only [ha, resume_found_preserves, hb, QuotaSearchResult.toOption,
        Option.some.injEq] at ho
      simp [resume_found_preserves, ho]
    | exhausted d =>
      simp [ha, resume_found_preserves, hb, QuotaSearchResult.toOption] at ho
  | exhausted c =>
    cases hr : resumeQuotaSearch (.exhausted c) b with
    | found t =>
      cases hb : startQuotaSearch n p j ε b with
      | found u =>
        simp only [ha, hr, hb, QuotaSearchResult.toOption, Option.some.injEq] at ho
        simp [ho]
      | exhausted d => simp [ha, hr, hb, QuotaSearchResult.toOption] at ho
    | exhausted d =>
      cases hb : startQuotaSearch n p j ε b with
      | found u => simp [ha, hr, hb, QuotaSearchResult.toOption] at ho
      | exhausted e =>
        have hcb := startQuotaSearch_bound n p j ε a c ha
        have hdb := resume_exhausted_bound c d b hr
        have heb := startQuotaSearch_bound n p j ε b e hb
        have hde : d.bound = e.bound := by rw [hdb, hcb, heb, Nat.max_eq_right hab]
        exact congrArg QuotaSearchResult.exhausted (cursor_ext d e hde)

/-- A separate initial cap makes the empty tail mean one cold start. -/
def lastCap (cap₀ : ℕ) (caps : List ℕ) : ℕ :=
  (cap₀ :: caps).getLast (List.cons_ne_nil _ _)

@[simp] theorem lastCap_nil (cap₀ : ℕ) : lastCap cap₀ [] = cap₀ := rfl

@[simp] theorem lastCap_cons (cap₀ c : ℕ) (caps : List ℕ) :
    lastCap cap₀ (c :: caps) = lastCap c caps := by
  simp [lastCap]

/-- Execute one continuation and add its actual counts to the accumulator. -/
def quotaResumeChainStep {n p j ε}
    (acc : QuotaSearchResult n p j ε × TabularStats) (cap : ℕ) :
    QuotaSearchResult n p j ε × TabularStats :=
  let next := resumeQuotaSearchInstrumented acc.1 cap
  (next.1, acc.2.add next.2)

/-- A left-to-right fold retaining the actual result of every step. -/
def quotaResumeChainFold {n p j ε}
    (acc : QuotaSearchResult n p j ε × TabularStats) : List ℕ →
    QuotaSearchResult n p j ε × TabularStats
  | [] => acc
  | c :: cs => quotaResumeChainFold (quotaResumeChainStep acc c) cs

def runQuotaResumeChainInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) : QuotaSearchResult n p j ε × TabularStats :=
  quotaResumeChainFold (startQuotaSearchInstrumented n p j ε cap₀) caps

/-- The full state and cost invariant after a single monotone step. -/
theorem chain_step_cold (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (a b : ℕ) (hab : a ≤ b) :
    quotaResumeChainStep (startQuotaSearch n p j ε a, streamingStats n p j ε a) b =
      (startQuotaSearch n p j ε b, streamingStats n p j ε b) := by
  apply Prod.ext
  · exact (resume_result _ b).trans (resumeQuotaSearch_startQuotaSearch n p j ε a b hab)
  · have h := two_stage_additive n p j ε a b hab
    simpa only [twoStageQuotaSearchInstrumented, start_result, start_cold_stats,
      quotaResumeChainStep] using h

/-- Induct once on the chain, keeping the entire state/cost pair. -/
theorem chain_fold_cold (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    quotaResumeChainFold (startQuotaSearch n p j ε cap₀, streamingStats n p j ε cap₀) caps =
      (startQuotaSearch n p j ε (lastCap cap₀ caps),
        streamingStats n p j ε (lastCap cap₀ caps)) := by
  induction caps generalizing cap₀ with
  | nil => rfl
  | cons c cs ih =>
    have h := List.isChain_cons_cons.mp hc
    rw [quotaResumeChainFold, chain_step_cold n p j ε cap₀ c h.1, lastCap_cons]
    exact ih c h.2

theorem chain_pair_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    runQuotaResumeChainInstrumented n p j ε cap₀ caps =
      (startQuotaSearch n p j ε (lastCap cap₀ caps),
        streamingStats n p j ε (lastCap cap₀ caps)) := by
  have h : startQuotaSearchInstrumented n p j ε cap₀ =
      (startQuotaSearch n p j ε cap₀, streamingStats n p j ε cap₀) :=
    Prod.ext (start_result n p j ε cap₀) (start_cold_stats n p j ε cap₀)
  rw [runQuotaResumeChainInstrumented, h]
  exact chain_fold_cold n p j ε cap₀ caps hc

theorem chain_result (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    (runQuotaResumeChainInstrumented n p j ε cap₀ caps).1 =
      startQuotaSearch n p j ε (lastCap cap₀ caps) :=
  congrArg Prod.fst (chain_pair_eq n p j ε cap₀ caps hc)

theorem chain_toOption (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    (runQuotaResumeChainInstrumented n p j ε cap₀ caps).1.toOption =
      chooseQuotaBudgetWithin n p j ε (lastCap cap₀ caps) := by
  rw [chain_result n p j ε cap₀ caps hc, startQuotaSearch_eq]

theorem chain_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    (runQuotaResumeChainInstrumented n p j ε cap₀ caps).2 =
      streamingStats n p j ε (lastCap cap₀ caps) :=
  congrArg Prod.snd (chain_pair_eq n p j ε cap₀ caps hc)

theorem chain_counts (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₀ : ℕ) (caps : List ℕ) (hc : List.IsChain (· ≤ ·) (cap₀ :: caps)) :
    let cap := lastCap cap₀ caps
    let t := (chooseQuotaBudgetWithin n p j ε cap).getD cap
    (runQuotaResumeChainInstrumented n p j ε cap₀ caps).2 = ⟨t + 1, 1, t, n * t⟩ := by
  rw [chain_stats n p j ε cap₀ caps hc]
  exact cold_counts n p j ε (lastCap cap₀ caps)

structure CryptoHiddenScalarQuotaChainContractSuite : Prop where
  bridge : ∀ n p j ε a b, a ≤ b →
    resumeQuotaSearch (startQuotaSearch n p j ε a) b = startQuotaSearch n p j ε b
  chain : ∀ n p j ε cap₀ caps, List.IsChain (· ≤ ·) (cap₀ :: caps) →
    runQuotaResumeChainInstrumented n p j ε cap₀ caps =
      (startQuotaSearch n p j ε (lastCap cap₀ caps), streamingStats n p j ε (lastCap cap₀ caps))

theorem verification_suite : CryptoHiddenScalarQuotaChainContractSuite where
  bridge := resumeQuotaSearch_startQuotaSearch
  chain := chain_pair_eq
end CryptoHiddenScalarQuotaChainContract

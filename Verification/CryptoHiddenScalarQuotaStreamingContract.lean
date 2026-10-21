/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaTabularContract

/-! Inclusive streaming search, retaining the current materialized quota row.
The equality is unconditional for rational profiles; no monotonicity, complexity
or measured performance claim is needed. -/
namespace CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaBudgetContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaTabularContract

/-- Read the requested state; states at or beyond the boundary are absorbed. -/
def quotaRowValue (n j : ℕ) (row : Vector ℚ (n + 1)) : ℚ :=
  if h : j < n then row[j]'(by omega) else 1

theorem quotaRowValue_correct (n : ℕ) (p : ℕ → ℚ) (T j : ℕ) :
    quotaRowValue n j (quotaRow n p T) = quotaLower n p T j :=
  quotaLowerTabular_eq n p T j

/-- Check the current budget before advancing. Fuel counts remaining transitions,
so zero fuel still checks the current row. No previous rows are recomputed. -/
def quotaStreamingScan (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) :
    ℕ → ℕ → Vector ℚ (n + 1) → Option ℕ
  | 0, T, row => if 1 - quotaRowValue n j row ≤ ε then some T else none
  | fuel + 1, T, row =>
    if 1 - quotaRowValue n j row ≤ ε then some T
    else quotaStreamingScan n p j ε fuel (T + 1) (quotaNextRow n p row)

/-- The row invariant is preserved by the actual transition used by the scan. -/
theorem quotaStreamingScan_row_step (n : ℕ) (p : ℕ → ℚ) (T : ℕ)
    (row : Vector ℚ (n + 1)) (hrow : row = quotaRow n p T) :
    quotaNextRow n p row = quotaRow n p (T + 1) := by
  rw [hrow]; rfl

/-- First feasible budget in the inclusive interval [T,T+fuel]. -/
theorem quotaStreamingScan_spec (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hrow : row = quotaRow n p T) :
    match quotaStreamingScan n p j ε fuel T row with
    | some k => T ≤ k ∧ k ≤ T + fuel ∧ quotaDeficit n p k j ≤ ε ∧
        ∀ i, T ≤ i → i < k → ε < quotaDeficit n p i j
    | none => ∀ i, T ≤ i → i ≤ T + fuel → ε < quotaDeficit n p i j := by
  subst row
  unfold quotaDeficit
  induction fuel generalizing T with
  | zero =>
    simp only [quotaStreamingScan, quotaRowValue_correct]
    split_ifs with h
    · exact ⟨le_rfl, by omega, h, by omega⟩
    · intro i hi hi'
      have : i = T := by omega
      subst i
      exact lt_of_not_ge h
  | succ fuel ih =>
    simp only [quotaStreamingScan, quotaRowValue_correct]
    split_ifs with h
    · exact ⟨le_rfl, by omega, h, by omega⟩
    · have hh := ih (T + 1)
      change (match quotaStreamingScan n p j ε fuel (T + 1) (quotaRow n p (T + 1)) with
        | some k => _ | none => _)
      cases hs : quotaStreamingScan n p j ε fuel (T + 1) (quotaRow n p (T + 1)) with
      | some k =>
        simp only [hs] at hh ⊢
        refine ⟨by omega, by omega, hh.2.2.1, ?_⟩
        intro i hi hik
        by_cases he : i = T
        · simpa [he] using lt_of_not_ge h
        · exact hh.2.2.2 i (by omega) hik
      | none =>
        simp only [hs] at hh ⊢
        intro i hi hi'
        by_cases he : i = T
        · simpa [he] using lt_of_not_ge h
        · exact hh i (by omega) (by omega)

/-- Inclusive ascending scan from budget zero, reusing each computed row. -/
def chooseQuotaBudgetStreamingWithin (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) : Option ℕ :=
  quotaStreamingScan n p j ε cap 0 (quotaInitialRow n)

/-- Exact Option equality for all rational profiles, tolerances and caps. -/
theorem chooseQuotaBudgetStreamingWithin_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) :
    chooseQuotaBudgetStreamingWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap := by
  have hs := quotaStreamingScan_spec n p j ε cap 0 (quotaInitialRow n) rfl
  have hr := searchThrough_spec (fun T => quotaDeficit n p T j ≤ ε) cap
  change (match chooseQuotaBudgetStreamingWithin n p j ε cap with
    | some k => _ | none => _) at hs
  change (match chooseQuotaBudgetWithin n p j ε cap with
    | some k => _ | none => _) at hr
  cases he : chooseQuotaBudgetStreamingWithin n p j ε cap <;>
    cases hf : chooseQuotaBudgetWithin n p j ε cap <;>
    simp only [he, hf, Nat.zero_add] at hs hr ⊢
  · rename_i k
    exact False.elim (not_lt_of_ge hr.2.1 (hs k (by omega) hr.1))
  · rename_i k
    exact False.elim (hr k hs.2.1 hs.2.2.1)
  · rename_i k l
    congr 1
    apply Nat.le_antisymm
    · by_contra h
      exact not_lt_of_ge hr.2.1 (hs.2.2.2 l (by omega) (by omega))
    · by_contra h
      exact hr.2.2 k (by omega) hs.2.2.1

structure CryptoHiddenScalarQuotaStreamingContractSuite : Prop where
  row_step : ∀ n p T row, row = quotaRow n p T →
    quotaNextRow n p row = quotaRow n p (T + 1)
  search : ∀ n p j ε cap,
    chooseQuotaBudgetStreamingWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap

theorem verification_suite : CryptoHiddenScalarQuotaStreamingContractSuite where
  row_step := quotaStreamingScan_row_step
  search := chooseQuotaBudgetStreamingWithin_eq
end CryptoHiddenScalarQuotaStreamingContract

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaBudgetContract

/-! Finite search for the exact least budget of the reference quota recursion.
A successful search is globally minimal; failure only excludes the supplied
finite window. Extension to larger budgets requires a probability profile.
This is not a minimum budget theorem for physical acquisition. -/
namespace CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaBudgetContract
open CryptoHiddenScalarQuotaDeficitContract

/-- Search all natural budgets from zero through `cap`, inclusively. -/
def chooseQuotaBudgetWithin (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) : Option ℕ :=
  searchThrough (fun T => quotaDeficit n p T j ≤ ε) cap

theorem chooseQuotaBudgetWithin_sound (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap T₀ : ℕ) (h : chooseQuotaBudgetWithin n p j ε cap = some T₀) :
    T₀ ≤ cap ∧ quotaDeficit n p T₀ j ≤ ε := by
  have hs := searchThrough_some _ cap T₀ h
  exact ⟨hs.1, hs.2.1⟩

/-- All smaller natural budgets fail, not merely a selected subset. -/
theorem chooseQuotaBudgetWithin_minimal (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap T₀ : ℕ) (h : chooseQuotaBudgetWithin n p j ε cap = some T₀) :
    ∀ t < T₀, ε < quotaDeficit n p t j := by
  have hs := searchThrough_some _ cap T₀ h
  exact fun t ht => lt_of_not_ge (hs.2.2 t ht)

/-- Failure excludes exactly the bounded window. -/
theorem chooseQuotaBudgetWithin_none_iff (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) : chooseQuotaBudgetWithin n p j ε cap = none ↔
    ∀ t ≤ cap, ε < quotaDeficit n p t j := by
  constructor
  · intro h t ht
    exact lt_of_not_ge (searchThrough_none _ cap h t ht)
  · intro hall
    cases hs : chooseQuotaBudgetWithin n p j ε cap with
    | none => rfl
    | some t =>
      have hh := chooseQuotaBudgetWithin_sound n p j ε cap t hs
      exact False.elim (not_lt_of_ge hh.2 (hall t hh.1))

theorem chooseQuotaBudgetWithin_exists_of_cap (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) (hc : quotaDeficit n p cap j ≤ ε) :
    ∃ T₀, chooseQuotaBudgetWithin n p j ε cap = some T₀ := by
  cases hs : chooseQuotaBudgetWithin n p j ε cap with
  | some t => exact ⟨t, rfl⟩
  | none =>
    exact False.elim (not_lt_of_ge hc
      ((chooseQuotaBudgetWithin_none_iff n p j ε cap).mp hs cap le_rfl))

/-- The previously verified geometric budget is a sufficient finite search cap. -/
theorem chooseQuotaBudgetWithin_exists_of_blocks (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (K : ℕ) (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hj : j < n)
    (hK : chooseBlockCount (∏ i ∈ Finset.Ico j n, p i) ε = some K) :
    ∃ T₀, chooseQuotaBudgetWithin n p j ε (K * (n - j)) = some T₀ ∧
      T₀ ≤ K * (n - j) := by
  have hc := selected_quota_deficit_le n (K * (n - j)) j K p ε hp hj hK le_rfl
  obtain ⟨t, ht⟩ := chooseQuotaBudgetWithin_exists_of_cap n p j ε _ hc
  exact ⟨t, ht, (chooseQuotaBudgetWithin_sound n p j ε _ t ht).1⟩

/-- Insufficient time gives deficit one even without probability ranges. -/
theorem selected_budget_lower (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap T₀ : ℕ) (h : chooseQuotaBudgetWithin n p j ε cap = some T₀)
    (_hj : j < n) (he : ε < 1) : n - j ≤ T₀ := by
  have hs := (chooseQuotaBudgetWithin_sound n p j ε cap T₀ h).2
  by_contra hn
  have hz := CryptoHiddenScalarQuotaProductContract.quota_insufficient n T₀ j p
    (by omega : j + T₀ < n)
  simp only [quotaDeficit, hz, sub_zero] at hs
  exact not_lt_of_ge hs he

/-- Only this extension to every larger budget needs the probability ranges. -/
theorem selected_budget_feasible_iff (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap T₀ : ℕ) (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1)
    (h : chooseQuotaBudgetWithin n p j ε cap = some T₀) (T : ℕ) :
    quotaDeficit n p T j ≤ ε ↔ T₀ ≤ T := by
  constructor
  · intro ht
    by_contra hn
    exact not_lt_of_ge ht (chooseQuotaBudgetWithin_minimal n p j ε cap T₀ h T (by omega))
  · intro ht
    exact (quota_deficit_budget_antitone n T₀ T j p hp ht).trans
      (chooseQuotaBudgetWithin_sound n p j ε cap T₀ h).2

/-- Zero is chosen whenever it is already feasible, without range assumptions. -/
theorem chooseQuotaBudgetWithin_zero (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap : ℕ) (hz : quotaDeficit n p 0 j ≤ ε) :
    chooseQuotaBudgetWithin n p j ε cap = some 0 := by
  cases hs : chooseQuotaBudgetWithin n p j ε cap with
  | none =>
    exact False.elim (not_lt_of_ge hz
      ((chooseQuotaBudgetWithin_none_iff n p j ε cap).mp hs 0 (Nat.zero_le _)))
  | some t =>
    have ht : t = 0 := by
      by_contra hn
      exact not_lt_of_ge hz (chooseQuotaBudgetWithin_minimal n p j ε cap t hs 0 (by omega))
    simp [ht]

theorem chooseQuotaBudgetWithin_absorbed (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap : ℕ) (hj : n ≤ j) (he : 0 ≤ ε) :
    chooseQuotaBudgetWithin n p j ε cap = some 0 :=
  chooseQuotaBudgetWithin_zero n p j ε cap (by simpa [quota_deficit_full n 0 j p hj] using he)

theorem chooseQuotaBudgetWithin_absorbed_negative (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) (hj : n ≤ j) (he : ε < 0) :
    chooseQuotaBudgetWithin n p j ε cap = none := by
  apply (chooseQuotaBudgetWithin_none_iff n p j ε cap).mpr
  intro t _
  simpa [quota_deficit_full n t j p hj] using he

theorem chooseQuotaBudgetWithin_negative (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (he : ε < 0) :
    chooseQuotaBudgetWithin n p j ε cap = none := by
  apply (chooseQuotaBudgetWithin_none_iff n p j ε cap).mpr
  intro t _
  exact he.trans_le (quota_deficit_range n t j p hp).1

structure CryptoHiddenScalarQuotaMinimumContractSuite : Prop where
  sound : ∀ n p j ε cap t, chooseQuotaBudgetWithin n p j ε cap = some t →
    t ≤ cap ∧ quotaDeficit n p t j ≤ ε
  minimal : ∀ n p j ε cap t, chooseQuotaBudgetWithin n p j ε cap = some t →
    ∀ i < t, ε < quotaDeficit n p i j
  window : ∀ n p j ε cap, chooseQuotaBudgetWithin n p j ε cap = none ↔
    ∀ t ≤ cap, ε < quotaDeficit n p t j
  feasible : ∀ n p j ε cap t, (∀ i < n, 0 ≤ p i ∧ p i ≤ 1) →
    chooseQuotaBudgetWithin n p j ε cap = some t →
    ∀ T, quotaDeficit n p T j ≤ ε ↔ t ≤ T

theorem verification_suite : CryptoHiddenScalarQuotaMinimumContractSuite where
  sound := chooseQuotaBudgetWithin_sound
  minimal := chooseQuotaBudgetWithin_minimal
  window := chooseQuotaBudgetWithin_none_iff
  feasible := selected_budget_feasible_iff
end CryptoHiddenScalarQuotaMinimumContract

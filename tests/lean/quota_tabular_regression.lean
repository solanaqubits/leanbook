/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarQuotaDeficitContract

private def half : ℕ → ℚ := fun _ => 1/2
private def mixed : ℕ → ℚ := fun i => if i = 0 then 1 else 1/2

-- Independent exact values, including immutable-row and invalid-profile checks.
example : (quotaInitialRow 0).toArray = #[1] := by decide +kernel
example : (quotaInitialRow 2).toArray = #[0, 0, 1] := by decide +kernel
example : (quotaRow 2 half 1).toArray = #[0, 1/2, 1] := by decide +kernel
example : (quotaRow 2 half 2).toArray = #[1/4, 3/4, 1] := by decide +kernel
example : quotaLowerTabular 0 (fun _ => -3) 3 0 = 1 := by decide +kernel
example : quotaLowerTabular 2 half 3 2 = 1 := by decide +kernel
example : quotaLowerTabular 2 half 3 7 = 1 := by decide +kernel
example : quotaLowerTabular 2 half 0 0 = 0 := by decide +kernel
example : quotaLowerTabular 2 half 1 0 = 0 := by decide +kernel
example : quotaLowerTabular 2 (fun _ => 0) 4 0 = 0 := by decide +kernel
example : quotaLowerTabular 2 (fun _ => 1) 2 0 = 1 := by decide +kernel
example : quotaLowerTabular 2 mixed 3 0 = 3/4 := by decide +kernel
example : quotaLowerTabular 1 (fun _ => 2) 1 0 = 2 := by decide +kernel
example : quotaLowerTabular 1 (fun _ => 2) 2 0 = 0 := by decide +kernel
example : quotaLowerTabular 1 (fun _ => -1) 1 0 = -1 := by decide +kernel
example : quotaLowerTabular 1 (fun _ => -1) 2 0 = -3 := by decide +kernel
example : quotaLowerTabular 2 (fun i => if i = 0 then -1 else 2) 2 0 = -2 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 0 (2/5) 4 = some 4 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 0 (1/8) 6 = some 6 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 0 (2/5) 3 = none := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 0 0 0 = none := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 0 1 0 = some 0 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 0 (3/2) 0 = some 0 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 0 half 0 0 0 = some 0 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 3 (-1) 4 = none := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 3 0 4 = some 0 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 half 0 (-1/4) 3 = none := by decide +kernel
example : chooseQuotaBudgetTabularWithin 2 (fun _ => 1) 0 0 2 = some 2 := by decide +kernel
example : chooseQuotaBudgetTabularWithin 1 (fun _ => 2) 0 (-1) 2 = some 1 := by decide +kernel
example : quotaDeficitTabular 2 half 4 0 = 5/16 := by decide +kernel
example : quotaLowerTabular 2 half 1 0 ≠ (1/2 : ℚ) * (1/2) := by decide +kernel
example : quotaLowerTabular 2 (fun i => if i < 2 then 1/2 else -99) 2 0 = 1/4 := by decide +kernel

-- Apply the unconditional equalities and reuse the reference search theorems.
example (n T i : ℕ) (p : ℕ → ℚ) (hi : i < n + 1) :
    (quotaRow n p T)[i] = quotaLower n p T i := quotaRow_correct n p T i hi
example (n T j : ℕ) (p : ℕ → ℚ) :
    quotaLowerTabular n p T j = quotaLower n p T j := quotaLowerTabular_eq n p T j
example (n j cap : ℕ) (p : ℕ → ℚ) (ε : ℚ) :
    chooseQuotaBudgetTabularWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap :=
  chooseQuotaBudgetTabularWithin_eq n p j ε cap
example (n j cap t : ℕ) (p : ℕ → ℚ) (ε : ℚ)
    (h : chooseQuotaBudgetTabularWithin n p j ε cap = some t) :
    ∀ i < t, ε < quotaDeficitTabular n p i j := by
  rw [chooseQuotaBudgetTabularWithin_eq] at h
  simpa only [quotaDeficitTabular_eq] using chooseQuotaBudgetWithin_minimal n p j ε cap t h
example (n j cap t T : ℕ) (p : ℕ → ℚ) (ε : ℚ)
    (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1)
    (h : chooseQuotaBudgetTabularWithin n p j ε cap = some t) :
    quotaDeficitTabular n p T j ≤ ε ↔ t ≤ T := by
  rw [chooseQuotaBudgetTabularWithin_eq] at h
  simpa only [quotaDeficitTabular_eq] using selected_budget_feasible_iff n p j ε cap t hp h T

-- Runtime checks exercise the materialized implementation; they are not proofs.
def main : IO Unit := do
  let checks : List Bool := [
    decide ((quotaInitialRow 0).toArray = #[1]),
    decide ((quotaInitialRow 2).toArray = #[0, 0, 1]),
    decide ((quotaRow 2 half 1).toArray = #[0, 1/2, 1]),
    decide ((quotaRow 2 half 2).toArray = #[1/4, 3/4, 1]),
    decide (quotaLowerTabular 0 (fun _ => -3) 3 0 = 1),
    decide (quotaLowerTabular 2 half 3 2 = 1),
    decide (quotaLowerTabular 2 half 3 7 = 1),
    decide (quotaLowerTabular 2 half 0 0 = 0),
    decide (quotaLowerTabular 2 half 1 0 = 0),
    decide (quotaLowerTabular 2 (fun _ => 0) 4 0 = 0),
    decide (quotaLowerTabular 2 (fun _ => 1) 2 0 = 1),
    decide (quotaLowerTabular 2 mixed 3 0 = 3/4),
    decide (quotaLowerTabular 1 (fun _ => 2) 1 0 = 2),
    decide (quotaLowerTabular 1 (fun _ => 2) 2 0 = 0),
    decide (quotaLowerTabular 1 (fun _ => -1) 1 0 = -1),
    decide (quotaLowerTabular 1 (fun _ => -1) 2 0 = -3),
    decide (quotaLowerTabular 2 (fun i => if i = 0 then -1 else 2) 2 0 = -2),
    decide (chooseQuotaBudgetTabularWithin 2 half 0 (2/5) 4 = some 4),
    decide (chooseQuotaBudgetTabularWithin 2 half 0 (1/8) 6 = some 6),
    decide (chooseQuotaBudgetTabularWithin 2 half 0 (2/5) 3 = none),
    decide (chooseQuotaBudgetTabularWithin 2 half 0 0 0 = none),
    decide (chooseQuotaBudgetTabularWithin 2 half 0 1 0 = some 0),
    decide (chooseQuotaBudgetTabularWithin 2 half 0 (3/2) 0 = some 0),
    decide (chooseQuotaBudgetTabularWithin 0 half 0 0 0 = some 0),
    decide (chooseQuotaBudgetTabularWithin 2 half 3 (-1) 4 = none),
    decide (chooseQuotaBudgetTabularWithin 2 half 3 0 4 = some 0),
    decide (chooseQuotaBudgetTabularWithin 2 half 0 (-1/4) 3 = none),
    decide (chooseQuotaBudgetTabularWithin 2 (fun _ => 1) 0 0 2 = some 2),
    decide (chooseQuotaBudgetTabularWithin 1 (fun _ => 2) 0 (-1) 2 = some 1),
    decide (quotaDeficitTabular 2 half 4 0 = 5/16),
    decide (quotaLowerTabular 2 half 1 0 ≠ (1/2 : ℚ) * (1/2)),
    decide (quotaLowerTabular 2 (fun i => if i < 2 then 1/2 else -99) 2 0 = 1/4)]
  unless checks.all id do
    throw (IO.userError "tabular quota regression failed")
  IO.println s!"QUOTA_TABULAR_OK {checks.length}"

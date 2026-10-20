/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaBudgetContract
open CryptoHiddenScalarQuotaDeficitContract

private def half : ℕ → ℚ := fun _ => 1/2
private def mixed : ℕ → ℚ := fun i => if i = 0 then 1 else 1/2

-- Compact exact kernel checks, independently of the IO assertions below.
example : chooseQuotaBudgetWithin 2 half 0 (2/5) 8 = some 4 := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 (1/8) 16 = some 6 := by decide +kernel
example : chooseBlockCount (1/4) (2/5) = some 4 := by decide +kernel
example : chooseBlockCount (1/4) (1/8) = some 8 := by decide +kernel
example : quotaDeficit 2 half 3 0 = 1/2 := by decide +kernel
example : quotaDeficit 2 half 4 0 = 5/16 := by decide +kernel
example : quotaDeficit 2 half 5 0 = 3/16 := by decide +kernel
example : quotaDeficit 2 half 6 0 = 7/64 := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 (2/5) 3 = none := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 (2/5) 4 = some 4 := by decide +kernel
example : chooseQuotaBudgetWithin 1 half 0 (1/8) 3 = some 3 := by decide +kernel
example : quotaDeficit 1 half 3 0 = 1/8 ∧ (1/8 : ℚ) < quotaDeficit 1 half 2 0 := by decide +kernel
example : chooseQuotaBudgetWithin 2 mixed 0 (1/4) 5 = some 3 := by decide +kernel
example : chooseQuotaBudgetWithin 2 (fun _ => 1) 0 0 2 = some 2 := by decide +kernel
example : chooseQuotaBudgetWithin 2 (fun _ => 0) 0 (1/2) 4 = none := by decide +kernel
example : chooseQuotaBudgetWithin 0 half 0 0 0 = some 0 := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 3 0 4 = some 0 := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 3 (-1) 4 = none := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 1 0 = some 0 := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 (3/2) 2 = some 0 := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 (-1/4) 3 = none := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 0 0 = none := by decide +kernel
example : chooseQuotaBudgetWithin 2 half 0 (1/2) 1 = none := by decide +kernel
example : chooseQuotaBudgetWithin 1 (fun _ => 2) 0 0 2 = some 1 := by decide +kernel
example : quotaDeficit 1 (fun _ => 2) 1 0 = -1 ∧
    quotaDeficit 1 (fun _ => 2) 2 0 = 1 := by decide +kernel

-- Apply each general result with its real hypotheses; no alternate recursion.
example (T : ℕ) : quotaDeficit 2 half T 0 ≤ 2/5 ↔ 4 ≤ T :=
  selected_budget_feasible_iff 2 half 0 (2/5) 8 4
    (by intro i _; norm_num [half]) (by decide +kernel) T
example : ∀ t < 6, (1/8 : ℚ) < quotaDeficit 2 half t 0 :=
  chooseQuotaBudgetWithin_minimal 2 half 0 (1/8) 16 6 (by decide +kernel)
example : ∀ t ≤ 3, (2/5 : ℚ) < quotaDeficit 2 half t 0 :=
  (chooseQuotaBudgetWithin_none_iff 2 half 0 (2/5) 3).mp (by decide +kernel)
example : ∃ t, chooseQuotaBudgetWithin 2 half 0 (2/5) 8 = some t ∧ t ≤ 8 := by
  simpa using chooseQuotaBudgetWithin_exists_of_blocks 2 half 0 (2/5) 4
    (by intro i _; norm_num [half]) (by decide +kernel) (by decide +kernel)
example (cap t : ℕ) (h : chooseQuotaBudgetWithin 2 (fun _ => 2) 0 0 cap = some t) :
    2 ≤ t := selected_budget_lower 2 _ 0 0 cap t h (by decide +kernel) (by decide +kernel)
example (cap : ℕ) : chooseQuotaBudgetWithin 2 half 2 0 cap = some 0 :=
  chooseQuotaBudgetWithin_absorbed 2 half 2 0 cap le_rfl le_rfl
example (cap : ℕ) : chooseQuotaBudgetWithin 2 half 2 (-1) cap = none :=
  chooseQuotaBudgetWithin_absorbed_negative 2 half 2 (-1) cap le_rfl (by decide +kernel)
example (cap : ℕ) : chooseQuotaBudgetWithin 2 half 0 (-1) cap = none :=
  chooseQuotaBudgetWithin_negative 2 half 0 (-1) cap
    (by intro i _; norm_num [half]) (by decide +kernel)

-- Twenty-five bounded runtime scenarios exercise the executable selector.
def main : IO Unit := do
  let checks : List Bool := [
    decide (chooseQuotaBudgetWithin 2 half 0 (2/5) 8 = some 4),
    decide (chooseQuotaBudgetWithin 2 half 0 (1/8) 16 = some 6),
    decide (chooseBlockCount (1/4) (2/5) = some 4),
    decide (chooseBlockCount (1/4) (1/8) = some 8),
    decide (quotaDeficit 2 half 3 0 = 1/2),
    decide (quotaDeficit 2 half 4 0 = 5/16),
    decide (quotaDeficit 2 half 5 0 = 3/16),
    decide (quotaDeficit 2 half 6 0 = 7/64),
    decide (chooseQuotaBudgetWithin 2 half 0 (2/5) 3 = none),
    decide (chooseQuotaBudgetWithin 2 half 0 (2/5) 4 = some 4),
    decide (chooseQuotaBudgetWithin 1 half 0 (1/8) 3 = some 3),
    decide (quotaDeficit 1 half 3 0 = 1/8 ∧ (1/8 : ℚ) < quotaDeficit 1 half 2 0),
    decide (chooseQuotaBudgetWithin 2 mixed 0 (1/4) 5 = some 3),
    decide (chooseQuotaBudgetWithin 2 (fun _ => 1) 0 0 2 = some 2),
    decide (chooseQuotaBudgetWithin 2 (fun _ => 0) 0 (1/2) 4 = none),
    decide (chooseQuotaBudgetWithin 0 half 0 0 0 = some 0),
    decide (chooseQuotaBudgetWithin 2 half 3 0 4 = some 0),
    decide (chooseQuotaBudgetWithin 2 half 3 (-1) 4 = none),
    decide (chooseQuotaBudgetWithin 2 half 0 1 0 = some 0),
    decide (chooseQuotaBudgetWithin 2 half 0 (3/2) 2 = some 0),
    decide (chooseQuotaBudgetWithin 2 half 0 (-1/4) 3 = none),
    decide (chooseQuotaBudgetWithin 2 half 0 0 0 = none),
    decide (chooseQuotaBudgetWithin 2 half 0 (1/2) 1 = none),
    decide (chooseQuotaBudgetWithin 1 (fun _ => 2) 0 0 2 = some 1),
    decide (quotaDeficit 1 (fun _ => 2) 1 0 = -1 ∧ quotaDeficit 1 (fun _ => 2) 2 0 = 1)]
  for c in checks do
    unless c do throw (IO.userError "quota minimum regression failed")
  IO.println s!"QUOTA_MINIMUM_OK {checks.length}"

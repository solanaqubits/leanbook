/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaTabularContract

def view {n p j ε} (r : QuotaSearchResult n p j ε) : Option (ℕ × List ℚ) :=
  match r with
  | .found _ => none
  | .exhausted c => some (c.bound, c.row.toList)

def half : ℕ → ℚ := fun _ => 1/2

example : (initQuotaSearch 0 half 0 0).toOption = some 0 := by decide +kernel

example : view (initQuotaSearch 0 half 0 (-1)) = some (0, [1]) := by decide +kernel

example : (initQuotaSearch 2 half 2 0).toOption = some 0 := by decide +kernel

example : view (startQuotaSearch 2 half 2 (-1) 2) = some (2, [1/4, 3/4, 1]) := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 half 3 (-1) 1) 3).toOption = none := by decide +kernel

example : (initQuotaSearch 2 half 0 1).toOption = some 0 := by decide +kernel

example : view (initQuotaSearch 2 half 0 (1/2)) = some (0, [0, 0, 1]) := by decide +kernel

example : view (startQuotaSearch 2 half 0 (2/5) 3) = some (3, [1/2, 7/8, 1]) := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 4).toOption = some 4 := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 5).toOption = some 4 := by decide +kernel

example : view (startQuotaSearch 2 half 0 (1/8) 5) = some (5, [13/16, 31/32, 1]) := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 half 0 (1/8) 5) 6).toOption = some 6 := by decide +kernel

example : view (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 3) = some (3, [1/2, 7/8, 1]) := by decide +kernel

example : view (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 1) = some (3, [1/2, 7/8, 1]) := by decide +kernel

example : (resumeQuotaSearch (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 2) 3) 4).toOption = some 4 := by decide +kernel

example : (resumeQuotaSearch (resumeQuotaSearch (initQuotaSearch 2 half 0 (1/8)) 5) 6).toOption = some 6 := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 4) 8).toOption = some 4 := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 1 (fun _ => 1) 0 0 1) 0).toOption = some 1 ∧ chooseQuotaBudgetWithin 1 (fun _ => 1) 0 0 0 = none := by decide +kernel

example : (resumeQuotaSearch (initQuotaSearch 1 (fun _ => 2) 0 (-1)) 1).toOption = some 1 := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 1 (fun _ => 2) 0 (-1) 1) 2).toOption = some 1 := by decide +kernel

example : view (resumeQuotaSearch (startQuotaSearch 1 (fun _ => -1) 0 0 1) 3) = some (3, [-7, 1]) := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 (fun i => if i = 0 then 1/2 else 1) 0 (1/2) 1) 2).toOption = some 2 := by decide +kernel

example : view (resumeQuotaSearch (startQuotaSearch 1 (fun _ => 0) 0 0 2) 4) = some (4, [0, 1]) := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 (fun _ => 1) 0 0 1) 2).toOption = some 2 := by decide +kernel

example : view (resumeQuotaSearch (startQuotaSearch 0 half 0 (-1) 2) 5) = some (5, [1]) := by decide +kernel

example : view (resumeQuotaSearch (startQuotaSearch 0 half 0 (-1) 5) 0) = some (5, [1]) := by decide +kernel

example : (resumeQuotaSearch (initQuotaSearch 0 half 0 0) 5).toOption = some 0 := by decide +kernel

example : (resumeQuotaSearch (.found 99 : QuotaSearchResult 1 half 0 0) 0).toOption = some 99 := by decide +kernel

example : view (startQuotaSearch 1 half 0 (-1) 0) = some (0, [0, 1]) := by decide +kernel

example : (startQuotaSearch 1 half 0 (1/2) 1).toOption = some 1 := by decide +kernel

example : (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 0).toOption = chooseQuotaBudgetWithin 2 half 0 (2/5) 0 := by decide +kernel

example : view (resumeQuotaSearch (resumeQuotaSearch (startQuotaSearch 1 (fun _ => 0) 0 0 4) 1) 5) = some (5, [0, 1]) := by decide +kernel

example (n p j ε cap₁ cap₂) (h : cap₁ ≤ cap₂) :
    (resumeQuotaSearch (startQuotaSearch n p j ε cap₁) cap₂).toOption =
      chooseQuotaBudgetWithin n p j ε cap₂ := resume_start_eq n p j ε cap₁ cap₂ h
example {n p j ε} (c : QuotaSearchCursor n p j ε) (cap : ℕ) :
    (resumeQuotaSearch (.exhausted c) cap).toOption = chooseQuotaBudgetWithin n p j ε cap :=
  resume_exhausted_eq c cap
example {n p j ε} (c : QuotaSearchCursor n p j ε) :
    c.row = quotaRow n p c.bound := c.row_correct
example {n p j ε} (c : QuotaSearchCursor n p j ε) :
    ∀ t ≤ c.bound, ε < CryptoHiddenScalarQuotaDeficitContract.quotaDeficit n p t j :=
  c.prefix_failed

def main : IO Unit := do
  let scenarios : List Bool := [
    decide ((initQuotaSearch 0 half 0 0).toOption = some 0),
    decide (view (initQuotaSearch 0 half 0 (-1)) = some (0, [1])),
    decide ((initQuotaSearch 2 half 2 0).toOption = some 0),
    decide (view (startQuotaSearch 2 half 2 (-1) 2) = some (2, [1/4, 3/4, 1])),
    decide ((resumeQuotaSearch (startQuotaSearch 2 half 3 (-1) 1) 3).toOption = none),
    decide ((initQuotaSearch 2 half 0 1).toOption = some 0),
    decide (view (initQuotaSearch 2 half 0 (1/2)) = some (0, [0, 0, 1])),
    decide (view (startQuotaSearch 2 half 0 (2/5) 3) = some (3, [1/2, 7/8, 1])),
    decide ((resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 4).toOption = some 4),
    decide ((resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 5).toOption = some 4),
    decide (view (startQuotaSearch 2 half 0 (1/8) 5) = some (5, [13/16, 31/32, 1])),
    decide ((resumeQuotaSearch (startQuotaSearch 2 half 0 (1/8) 5) 6).toOption = some 6),
    decide (view (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 3) = some (3, [1/2, 7/8, 1])),
    decide (view (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 1) = some (3, [1/2, 7/8, 1])),
    decide ((resumeQuotaSearch (resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 2) 3) 4).toOption = some 4),
    decide ((resumeQuotaSearch (resumeQuotaSearch (initQuotaSearch 2 half 0 (1/8)) 5) 6).toOption = some 6),
    decide ((resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 4) 8).toOption = some 4),
    decide ((resumeQuotaSearch (startQuotaSearch 1 (fun _ => 1) 0 0 1) 0).toOption = some 1 ∧ chooseQuotaBudgetWithin 1 (fun _ => 1) 0 0 0 = none),
    decide ((resumeQuotaSearch (initQuotaSearch 1 (fun _ => 2) 0 (-1)) 1).toOption = some 1),
    decide ((resumeQuotaSearch (startQuotaSearch 1 (fun _ => 2) 0 (-1) 1) 2).toOption = some 1),
    decide (view (resumeQuotaSearch (startQuotaSearch 1 (fun _ => -1) 0 0 1) 3) = some (3, [-7, 1])),
    decide ((resumeQuotaSearch (startQuotaSearch 2 (fun i => if i = 0 then 1/2 else 1) 0 (1/2) 1) 2).toOption = some 2),
    decide (view (resumeQuotaSearch (startQuotaSearch 1 (fun _ => 0) 0 0 2) 4) = some (4, [0, 1])),
    decide ((resumeQuotaSearch (startQuotaSearch 2 (fun _ => 1) 0 0 1) 2).toOption = some 2),
    decide (view (resumeQuotaSearch (startQuotaSearch 0 half 0 (-1) 2) 5) = some (5, [1])),
    decide (view (resumeQuotaSearch (startQuotaSearch 0 half 0 (-1) 5) 0) = some (5, [1])),
    decide ((resumeQuotaSearch (initQuotaSearch 0 half 0 0) 5).toOption = some 0),
    decide ((resumeQuotaSearch (.found 99 : QuotaSearchResult 1 half 0 0) 0).toOption = some 99),
    decide (view (startQuotaSearch 1 half 0 (-1) 0) = some (0, [0, 1])),
    decide ((startQuotaSearch 1 half 0 (1/2) 1).toOption = some 1),
    decide ((resumeQuotaSearch (startQuotaSearch 2 half 0 (2/5) 3) 0).toOption = chooseQuotaBudgetWithin 2 half 0 (2/5) 0),
    decide (view (resumeQuotaSearch (resumeQuotaSearch (startQuotaSearch 1 (fun _ => 0) 0 0 4) 1) 5) = some (5, [0, 1]))]
  for passed in scenarios do
    unless passed do throw (IO.userError "quota resumable scenario failed")
  IO.println s!"QUOTA_RESUMABLE_OK {scenarios.length}"

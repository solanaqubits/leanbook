/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaTabularContract

example : chooseQuotaBudgetTabularInstrumented 0 (fun _ => 1/2) 0 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 0 (fun _ => 1/2) 0 (-1) 3 = (none, ⟨4, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 3 (0) 3 = (some 0, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 3 (-1) 3 = (none, ⟨4, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (0) 0 = (none, ⟨1, 1, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (1) 0 = (some 0, ⟨1, 1, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 1 (fun _ => 1) 0 (0) 4 = (some 1, ⟨2, 2, 1, 1⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 1 (fun _ => 0) 0 (1/2) 3 = (none, ⟨4, 4, 6, 6⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 1 (fun _ => 1/2) 0 (1/4) 5 = (some 2, ⟨3, 3, 3, 3⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (2/5) 6 = (some 4, ⟨5, 5, 10, 20⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (1/8) 8 = (some 6, ⟨7, 7, 21, 42⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (2/5) 3 = (none, ⟨4, 4, 6, 12⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 1 (fun _ => 2) 0 (-1) 4 = (some 1, ⟨2, 2, 1, 1⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 1 (fun _ => -1) 0 (0) 3 = (none, ⟨4, 4, 6, 6⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 1 (fun _ => 2) 0 (-2) 3 = (none, ⟨4, 4, 6, 6⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 3 (fun _ => 1) 1 (0) 4 = (some 2, ⟨3, 3, 3, 9⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1) 0 (0) 1 = (none, ⟨2, 2, 1, 2⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1) 0 (0) 2 = (some 2, ⟨3, 3, 3, 6⟩) := by decide +kernel

example : chooseQuotaBudgetTabularInstrumented 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/2) 4 = (some 2, ⟨3, 3, 3, 6⟩) := by decide +kernel

example : (quotaRowInstrumented 2 (fun _ => 1/2) 2).2 = ⟨0, 1, 2, 4⟩ := by decide +kernel

example : (quotaRowInstrumented 2 (fun _ => 1/2) 2).1 = #v[1/4, 3/4, 1] := by decide +kernel

example : streamingStats 2 (fun _ => 1/2) 3 (-1) 3 = ⟨4, 1, 3, 6⟩ := by decide +kernel

example : streamingStats 0 (fun _ => 1/2) 0 (-1) 3 = ⟨4, 1, 3, 0⟩ := by decide +kernel

example : streamingStats 2 (fun _ => 1/2) 3 0 3 = ⟨1, 1, 0, 0⟩ := by decide +kernel

example : streamingStats 2 (fun _ => 1/2) 0 (2/5) 6 = ⟨5, 1, 4, 8⟩ := by decide +kernel

example : streamingStats 2 (fun _ => 1/2) 0 (1/8) 8 = ⟨7, 1, 6, 12⟩ := by decide +kernel

example : triangular 0 = 0 ∧ triangular 1 = 1 ∧ triangular 2 = 3 := by decide +kernel

example : triangular 4 - 4 = 6 ∧ triangular 6 - 6 = 15 := by decide +kernel

example : (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 3 (-1) 3).2.transitions < (streamingStats 2 (fun _ => 1/2) 3 (-1) 3).transitions := by decide +kernel

example : (chooseQuotaBudgetTabularInstrumented 1 (fun _ => 1) 0 0 4).2.transitions = (streamingStats 1 (fun _ => 1) 0 0 4).transitions := by decide +kernel

example (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 = chooseQuotaBudgetTabularWithin n p j ε cap :=
  chooseQuotaBudgetTabularInstrumented_eq n p j ε cap
example (t : ℕ) : triangular t - t = t*(t-1)/2 := triangular_saving t

def main : IO Unit := do
  let scenarios : List Bool := [
    decide (chooseQuotaBudgetTabularInstrumented 0 (fun _ => 1/2) 0 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 0 (fun _ => 1/2) 0 (-1) 3 = (none, ⟨4, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 3 (0) 3 = (some 0, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 3 (-1) 3 = (none, ⟨4, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (0) 0 = (none, ⟨1, 1, 0, 0⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (1) 0 = (some 0, ⟨1, 1, 0, 0⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 1 (fun _ => 1) 0 (0) 4 = (some 1, ⟨2, 2, 1, 1⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 1 (fun _ => 0) 0 (1/2) 3 = (none, ⟨4, 4, 6, 6⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 1 (fun _ => 1/2) 0 (1/4) 5 = (some 2, ⟨3, 3, 3, 3⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (2/5) 6 = (some 4, ⟨5, 5, 10, 20⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (1/8) 8 = (some 6, ⟨7, 7, 21, 42⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 0 (2/5) 3 = (none, ⟨4, 4, 6, 12⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 1 (fun _ => 2) 0 (-1) 4 = (some 1, ⟨2, 2, 1, 1⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 1 (fun _ => -1) 0 (0) 3 = (none, ⟨4, 4, 6, 6⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 1 (fun _ => 2) 0 (-2) 3 = (none, ⟨4, 4, 6, 6⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 3 (fun _ => 1) 1 (0) 4 = (some 2, ⟨3, 3, 3, 9⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1) 0 (0) 1 = (none, ⟨2, 2, 1, 2⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1) 0 (0) 2 = (some 2, ⟨3, 3, 3, 6⟩)),
    decide (chooseQuotaBudgetTabularInstrumented 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/2) 4 = (some 2, ⟨3, 3, 3, 6⟩)),
    decide ((quotaRowInstrumented 2 (fun _ => 1/2) 2).2 = ⟨0, 1, 2, 4⟩),
    decide ((quotaRowInstrumented 2 (fun _ => 1/2) 2).1 = #v[1/4, 3/4, 1]),
    decide (streamingStats 2 (fun _ => 1/2) 3 (-1) 3 = ⟨4, 1, 3, 6⟩),
    decide (streamingStats 0 (fun _ => 1/2) 0 (-1) 3 = ⟨4, 1, 3, 0⟩),
    decide (streamingStats 2 (fun _ => 1/2) 3 0 3 = ⟨1, 1, 0, 0⟩),
    decide (streamingStats 2 (fun _ => 1/2) 0 (2/5) 6 = ⟨5, 1, 4, 8⟩),
    decide (streamingStats 2 (fun _ => 1/2) 0 (1/8) 8 = ⟨7, 1, 6, 12⟩),
    decide (triangular 0 = 0 ∧ triangular 1 = 1 ∧ triangular 2 = 3),
    decide (triangular 4 - 4 = 6 ∧ triangular 6 - 6 = 15),
    decide ((chooseQuotaBudgetTabularInstrumented 2 (fun _ => 1/2) 3 (-1) 3).2.transitions < (streamingStats 2 (fun _ => 1/2) 3 (-1) 3).transitions),
    decide ((chooseQuotaBudgetTabularInstrumented 1 (fun _ => 1) 0 0 4).2.transitions = (streamingStats 1 (fun _ => 1) 0 0 4).transitions)]
  unless scenarios.all id do throw (IO.userError "quota comparison regression failed")
  IO.println s!"QUOTA_COMPARISON_OK {scenarios.length}"

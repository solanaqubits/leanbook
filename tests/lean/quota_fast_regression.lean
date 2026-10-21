/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaFastContract
open CryptoHiddenScalarQuotaFastContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaComparisonContract

example : chooseQuotaBudgetFastInstrumented 0 (fun _ => 1/2) 0 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 0 (fun _ => 1/2) 0 (-1) 5 = (none, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 2 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 2 (-1) 5 = (none, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 3 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 3 (-1) 5 = (none, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2) 0 = (some 0, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1) 0 = (some 0, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1/2) 0 = (none, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (0) 0 = (none, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (-1) 0 = (none, ⟨1, 0, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 1 (fun _ => 2) 0 (-1) 4 = (some 1, ⟨2, 1, 1, 1⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 1 (fun _ => 2) 0 (-2) 3 = (none, ⟨4, 1, 3, 3⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 1 (fun _ => -1) 0 (0) 3 = (none, ⟨4, 1, 3, 3⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2/5) 6 = (some 4, ⟨5, 1, 4, 8⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1/8) 8 = (some 6, ⟨7, 1, 6, 12⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2/5) 3 = (none, ⟨4, 1, 3, 6⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2/5) 4 = (some 4, ⟨5, 1, 4, 8⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1) 3 = (some 0, ⟨1, 1, 0, 0⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 2 (fun _ => 1) 0 (0) 2 = (some 2, ⟨3, 1, 2, 4⟩) := by decide +kernel

example : chooseQuotaBudgetFastInstrumented 1 (fun _ => 0) 0 (0) 2 = (none, ⟨3, 1, 2, 2⟩) := by decide +kernel

example : chooseQuotaBudgetFastWithin 1 (fun _ => 2) 0 (-1) 1 = chooseQuotaBudgetFastWithin 1 (fun _ => 2) 0 (-1) 2 := by decide +kernel

example : quotaDeficit 1 (fun _ => 2) 1 0 = -1 ∧ quotaDeficit 1 (fun _ => 2) 2 0 = 1 := by decide +kernel

example : chooseQuotaBudgetFastWithin 2 (fun _ => 1/2) 0 (1/8) 5 = none ∧ chooseQuotaBudgetFastWithin 2 (fun _ => 1/2) 0 (1/8) 6 = some 6 := by decide +kernel

example : (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 2 (-1) 5).2.transitions = 0 ∧ (streamingStats 2 (fun _ => 1/2) 2 (-1) 5).transitions = 5 := by decide +kernel

example : (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 0 0).2.inits = 0 ∧ (streamingStats 2 (fun _ => 1/2) 0 0 0).inits = 1 := by decide +kernel

example (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    chooseQuotaBudgetFastWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap :=
  chooseQuotaBudgetFastWithin_eq n p j ε cap
example (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap₁ cap₂ t : ℕ)
    (hc : cap₁ ≤ cap₂) (hs : chooseQuotaBudgetFastWithin n p j ε cap₁ = some t) :
    chooseQuotaBudgetFastWithin n p j ε cap₂ = some t :=
  chooseQuotaBudgetFastWithin_extend_some n p j ε cap₁ cap₂ t hc hs

def main : IO Unit := do
  let scenarios : List Bool := [
    decide (chooseQuotaBudgetFastInstrumented 0 (fun _ => 1/2) 0 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 0 (fun _ => 1/2) 0 (-1) 5 = (none, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 2 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 2 (-1) 5 = (none, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 3 (0) 5 = (some 0, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 3 (-1) 5 = (none, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2) 0 = (some 0, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1) 0 = (some 0, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1/2) 0 = (none, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (0) 0 = (none, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (-1) 0 = (none, ⟨1, 0, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 1 (fun _ => 2) 0 (-1) 4 = (some 1, ⟨2, 1, 1, 1⟩)),
    decide (chooseQuotaBudgetFastInstrumented 1 (fun _ => 2) 0 (-2) 3 = (none, ⟨4, 1, 3, 3⟩)),
    decide (chooseQuotaBudgetFastInstrumented 1 (fun _ => -1) 0 (0) 3 = (none, ⟨4, 1, 3, 3⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2/5) 6 = (some 4, ⟨5, 1, 4, 8⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1/8) 8 = (some 6, ⟨7, 1, 6, 12⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2/5) 3 = (none, ⟨4, 1, 3, 6⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (2/5) 4 = (some 4, ⟨5, 1, 4, 8⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 (1) 3 = (some 0, ⟨1, 1, 0, 0⟩)),
    decide (chooseQuotaBudgetFastInstrumented 2 (fun _ => 1) 0 (0) 2 = (some 2, ⟨3, 1, 2, 4⟩)),
    decide (chooseQuotaBudgetFastInstrumented 1 (fun _ => 0) 0 (0) 2 = (none, ⟨3, 1, 2, 2⟩)),
    decide (chooseQuotaBudgetFastWithin 1 (fun _ => 2) 0 (-1) 1 = chooseQuotaBudgetFastWithin 1 (fun _ => 2) 0 (-1) 2),
    decide (quotaDeficit 1 (fun _ => 2) 1 0 = -1 ∧ quotaDeficit 1 (fun _ => 2) 2 0 = 1),
    decide (chooseQuotaBudgetFastWithin 2 (fun _ => 1/2) 0 (1/8) 5 = none ∧ chooseQuotaBudgetFastWithin 2 (fun _ => 1/2) 0 (1/8) 6 = some 6),
    decide ((chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 2 (-1) 5).2.transitions = 0 ∧ (streamingStats 2 (fun _ => 1/2) 2 (-1) 5).transitions = 5),
    decide ((chooseQuotaBudgetFastInstrumented 2 (fun _ => 1/2) 0 0 0).2.inits = 0 ∧ (streamingStats 2 (fun _ => 1/2) 0 0 0).inits = 1)]
  unless scenarios.all id do throw (IO.userError "quota fast regression failed")
  IO.println s!"QUOTA_FAST_OK {scenarios.length}"

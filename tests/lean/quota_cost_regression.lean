/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaCostContract
open CryptoHiddenScalarQuotaCostContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarQuotaMinimumContract

example : chooseQuotaBudgetInstrumented 0 (fun _ => (1/2)) 0 (0) 5 = (some 0, ⟨1, 0, 0⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 0 (fun _ => (1/2)) 0 (-1) 3 = (none, ⟨4, 3, 0⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 3 (0) 3 = (some 0, ⟨1, 0, 0⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 3 (-1) 3 = (none, ⟨4, 3, 6⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (0) 0 = (none, ⟨1, 0, 0⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (1) 0 = (some 0, ⟨1, 0, 0⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 1 (fun _ => (1)) 0 (0) 4 = (some 1, ⟨2, 1, 1⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 1 (fun _ => (0)) 0 (1/2) 3 = (none, ⟨4, 3, 3⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 1 (fun _ => (1/2)) 0 (1/4) 5 = (some 2, ⟨3, 2, 2⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (2/5) 6 = (some 4, ⟨5, 4, 8⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (1/8) 8 = (some 6, ⟨7, 6, 12⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (2/5) 3 = (none, ⟨4, 3, 6⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 1 (fun _ => (2)) 0 (-1) 4 = (some 1, ⟨2, 1, 1⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 1 (fun _ => (-1)) 0 (0) 3 = (none, ⟨4, 3, 3⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 1 (fun _ => (2)) 0 (-2) 3 = (none, ⟨4, 3, 3⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 3 (fun _ => (1)) 1 (0) 4 = (some 2, ⟨3, 2, 6⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1)) 0 (0) 1 = (none, ⟨2, 1, 2⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (1)) 0 (0) 2 = (some 2, ⟨3, 2, 4⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun _ => (-1)) 0 (2) 4 = (some 0, ⟨1, 0, 0⟩)
  := by decide +kernel

example : chooseQuotaBudgetInstrumented 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/2) 4 = (some 2,
  ⟨3, 2, 4⟩) := by decide +kernel

example : quotaInstrumentedScan 1 (fun _ => 2) 0 (-1) 3 5 (quotaInitialRow 1) = (some 6, ⟨2, 1, 1⟩)
  := by decide +kernel

example : quotaInstrumentedScan 2 (fun _ => 1/2) 0 1 3 7 (quotaInitialRow 2) = (some 7, ⟨1, 0, 0⟩)
  := by decide +kernel

example : (quotaNextRowCounted 2 (fun _ => 1/2) (quotaInitialRow 2)).1 = #v[0, 1/2, 1]
  := by decide +kernel

example : (quotaNextRowCounted 0 (fun _ => -1) (quotaInitialRow 0)).2 = 0 := by decide +kernel

example : structuralCost 0 (chooseQuotaBudgetInstrumented 0 (fun _ => 1) 0 (-1) 3).2 = 8
  := by decide +kernel

example : structuralCost 2 (chooseQuotaBudgetInstrumented 2 (fun _ => 1/2) 0 (2/5) 6).2 = 20
  := by decide +kernel

example (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetInstrumented n p j ε cap).1 = chooseQuotaBudgetWithin n p j ε cap :=
  chooseQuotaBudgetInstrumented_eq_reference n p j ε cap
example (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    structuralCost n (chooseQuotaBudgetInstrumented n p j ε cap).2 ≤ 2*(n+1)*(cap+1) :=
  structuralCost_bound n p j ε cap

def main : IO Unit := do
  let scenarios : List Bool := [
    decide (chooseQuotaBudgetInstrumented 0 (fun _ => (1/2)) 0 (0) 5 = (some 0, ⟨1, 0, 0⟩)),
    decide (chooseQuotaBudgetInstrumented 0 (fun _ => (1/2)) 0 (-1) 3 = (none, ⟨4, 3, 0⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 3 (0) 3 = (some 0, ⟨1, 0, 0⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 3 (-1) 3 = (none, ⟨4, 3, 6⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (0) 0 = (none, ⟨1, 0, 0⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (1) 0 = (some 0, ⟨1, 0, 0⟩)),
    decide (chooseQuotaBudgetInstrumented 1 (fun _ => (1)) 0 (0) 4 = (some 1, ⟨2, 1, 1⟩)),
    decide (chooseQuotaBudgetInstrumented 1 (fun _ => (0)) 0 (1/2) 3 = (none, ⟨4, 3, 3⟩)),
    decide (chooseQuotaBudgetInstrumented 1 (fun _ => (1/2)) 0 (1/4) 5 = (some 2, ⟨3, 2, 2⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (2/5) 6 = (some 4, ⟨5, 4, 8⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (1/8) 8 = (some 6, ⟨7, 6, 12⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1/2)) 0 (2/5) 3 = (none, ⟨4, 3, 6⟩)),
    decide (chooseQuotaBudgetInstrumented 1 (fun _ => (2)) 0 (-1) 4 = (some 1, ⟨2, 1, 1⟩)),
    decide (chooseQuotaBudgetInstrumented 1 (fun _ => (-1)) 0 (0) 3 = (none, ⟨4, 3, 3⟩)),
    decide (chooseQuotaBudgetInstrumented 1 (fun _ => (2)) 0 (-2) 3 = (none, ⟨4, 3, 3⟩)),
    decide (chooseQuotaBudgetInstrumented 3 (fun _ => (1)) 1 (0) 4 = (some 2, ⟨3, 2, 6⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1)) 0 (0) 1 = (none, ⟨2, 1, 2⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (1)) 0 (0) 2 = (some 2, ⟨3, 2, 4⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun _ => (-1)) 0 (2) 4 = (some 0, ⟨1, 0, 0⟩)),
    decide (chooseQuotaBudgetInstrumented 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/2) 4 = (some 2,
      ⟨3, 2, 4⟩)),
    decide (quotaInstrumentedScan 1 (fun _ => 2) 0 (-1) 3 5 (quotaInitialRow 1) = (some 6, ⟨2, 1,
      1⟩)),
    decide (quotaInstrumentedScan 2 (fun _ => 1/2) 0 1 3 7 (quotaInitialRow 2) = (some 7, ⟨1, 0,
      0⟩)),
    decide ((quotaNextRowCounted 2 (fun _ => 1/2) (quotaInitialRow 2)).1 = #v[0, 1/2, 1]),
    decide ((quotaNextRowCounted 0 (fun _ => -1) (quotaInitialRow 0)).2 = 0),
    decide (structuralCost 0 (chooseQuotaBudgetInstrumented 0 (fun _ => 1) 0 (-1) 3).2 = 8),
    decide (structuralCost 2 (chooseQuotaBudgetInstrumented 2 (fun _ => 1/2) 0 (2/5) 6).2 = 20)]
  unless scenarios.all id do throw (IO.userError "quota cost regression failed")
  IO.println s!"QUOTA_COST_OK {scenarios.length}"

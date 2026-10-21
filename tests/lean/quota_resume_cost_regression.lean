/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaComparisonContract

def half : ℕ → ℚ := fun _ => 1/2

def view {n p j ε} (r : QuotaSearchResult n p j ε) : Option (ℕ × List ℚ) :=
  match r with
  | .found _ => none
  | .exhausted c => some (c.bound, c.row.toList)

example : (startQuotaSearchInstrumented 2 half 0 0 0).2 = (⟨1, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : (startQuotaSearchInstrumented 2 half 0 1 0).1.toOption = some 0 := by decide +kernel

example : (startQuotaSearchInstrumented 0 half 0 (-1) 3).2 = (⟨4, 1, 3, 0⟩ : TabularStats) := by decide +kernel

example : (startQuotaSearchInstrumented 2 half 2 0 3).2 = (⟨1, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 0 0) 0).2 = (⟨0, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 4).2 = (⟨1, 0, 1, 2⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 4).1.toOption = some 4 := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 5).2 = (⟨1, 0, 1, 2⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (1/8) 4) 6).2 = (⟨2, 0, 2, 4⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (1/8) 4) 6).1.toOption = some 6 := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 0) 0 0 2) 5).2 = (⟨3, 0, 3, 3⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 0) 0 0 2) 1).2 = (⟨0, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 0 half 0 (-1) 2) 5).2 = (⟨3, 0, 3, 0⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 2 (-1) 2) 4).2 = (⟨2, 0, 2, 4⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 1) 0 0 1) 0).2 = (⟨0, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (.found 99 : QuotaSearchResult 1 half 0 0) 100).2 = (⟨0, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 2) 0 (-1) 0) 2).2 = (⟨1, 0, 1, 1⟩ : TabularStats) := by decide +kernel

example : (resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => -1) 0 0 0) 3).2 = (⟨3, 0, 3, 3⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 2 half 0 (2/5) 4 6).2 = (⟨5, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 2 half 0 (2/5) 3 4).2 = (⟨5, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 1 (fun _ => 0) 0 0 2 5).2 = (⟨6, 1, 5, 5⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 2 half 0 (2/5) 3 3).2 = (⟨4, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 2 half 2 0 2 5).2 = (⟨1, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 0 half 0 (-1) 2 5).2 = (⟨6, 1, 5, 0⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 1 (fun _ => 2) 0 (-1) 0 2).2 = (⟨2, 1, 1, 1⟩ : TabularStats) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 1 (fun _ => 0) 0 0 2 1).2 ≠ streamingStats 1 (fun _ => 0) 0 0 1 := by decide +kernel

example : (twoStageQuotaSearchInstrumented 1 (fun _ => 1) 0 0 1 0).2 ≠ streamingStats 1 (fun _ => 1) 0 0 0 := by decide +kernel

example : view (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 1).1 = some (3, [1/2, 7/8, 1]) := by decide +kernel

example : view (resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 0) 0 0 2) 4).1 = some (4, [0, 1]) := by decide +kernel

example : (twoStageQuotaSearchInstrumented 2 half 0 (1/8) 5 6).2 = streamingStats 2 half 0 (1/8) 6 := by decide +kernel

example (n p j ε cap) : (startQuotaSearchInstrumented n p j ε cap).1 =
    startQuotaSearch n p j ε cap := start_result n p j ε cap
example {n p j ε} (r : QuotaSearchResult n p j ε) (cap : ℕ) :
    (resumeQuotaSearchInstrumented r cap).1 = resumeQuotaSearch r cap := resume_result r cap
example (n p j ε a b) (h : a ≤ b) :
    (twoStageQuotaSearchInstrumented n p j ε a b).2 = streamingStats n p j ε b :=
  two_stage_additive n p j ε a b h
example {n p j ε} (c : QuotaSearchCursor n p j ε) (cap : ℕ) (h : cap ≤ c.bound) :
    resumeQuotaSearchInstrumented (.exhausted c) cap = (.exhausted c, ⟨0, 0, 0, 0⟩) :=
  resume_covered c cap h

def main : IO Unit := do
  if !(decide ((startQuotaSearchInstrumented 2 half 0 0 0).2 = (⟨1, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 1")
  if !(decide ((startQuotaSearchInstrumented 2 half 0 1 0).1.toOption = some 0)) then throw (IO.userError "resume-cost case 2")
  if !(decide ((startQuotaSearchInstrumented 0 half 0 (-1) 3).2 = (⟨4, 1, 3, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 3")
  if !(decide ((startQuotaSearchInstrumented 2 half 2 0 3).2 = (⟨1, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 4")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 0 0) 0).2 = (⟨0, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 5")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 4).2 = (⟨1, 0, 1, 2⟩ : TabularStats))) then throw (IO.userError "resume-cost case 6")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 4).1.toOption = some 4)) then throw (IO.userError "resume-cost case 7")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 5).2 = (⟨1, 0, 1, 2⟩ : TabularStats))) then throw (IO.userError "resume-cost case 8")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (1/8) 4) 6).2 = (⟨2, 0, 2, 4⟩ : TabularStats))) then throw (IO.userError "resume-cost case 9")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (1/8) 4) 6).1.toOption = some 6)) then throw (IO.userError "resume-cost case 10")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 0) 0 0 2) 5).2 = (⟨3, 0, 3, 3⟩ : TabularStats))) then throw (IO.userError "resume-cost case 11")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 0) 0 0 2) 1).2 = (⟨0, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 12")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 0 half 0 (-1) 2) 5).2 = (⟨3, 0, 3, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 13")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 2 half 2 (-1) 2) 4).2 = (⟨2, 0, 2, 4⟩ : TabularStats))) then throw (IO.userError "resume-cost case 14")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 1) 0 0 1) 0).2 = (⟨0, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 15")
  if !(decide ((resumeQuotaSearchInstrumented (.found 99 : QuotaSearchResult 1 half 0 0) 100).2 = (⟨0, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 16")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 2) 0 (-1) 0) 2).2 = (⟨1, 0, 1, 1⟩ : TabularStats))) then throw (IO.userError "resume-cost case 17")
  if !(decide ((resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => -1) 0 0 0) 3).2 = (⟨3, 0, 3, 3⟩ : TabularStats))) then throw (IO.userError "resume-cost case 18")
  if !(decide ((twoStageQuotaSearchInstrumented 2 half 0 (2/5) 4 6).2 = (⟨5, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "resume-cost case 19")
  if !(decide ((twoStageQuotaSearchInstrumented 2 half 0 (2/5) 3 4).2 = (⟨5, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "resume-cost case 20")
  if !(decide ((twoStageQuotaSearchInstrumented 1 (fun _ => 0) 0 0 2 5).2 = (⟨6, 1, 5, 5⟩ : TabularStats))) then throw (IO.userError "resume-cost case 21")
  if !(decide ((twoStageQuotaSearchInstrumented 2 half 0 (2/5) 3 3).2 = (⟨4, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "resume-cost case 22")
  if !(decide ((twoStageQuotaSearchInstrumented 2 half 2 0 2 5).2 = (⟨1, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 23")
  if !(decide ((twoStageQuotaSearchInstrumented 0 half 0 (-1) 2 5).2 = (⟨6, 1, 5, 0⟩ : TabularStats))) then throw (IO.userError "resume-cost case 24")
  if !(decide ((twoStageQuotaSearchInstrumented 1 (fun _ => 2) 0 (-1) 0 2).2 = (⟨2, 1, 1, 1⟩ : TabularStats))) then throw (IO.userError "resume-cost case 25")
  if !(decide ((twoStageQuotaSearchInstrumented 1 (fun _ => 0) 0 0 2 1).2 ≠ streamingStats 1 (fun _ => 0) 0 0 1)) then throw (IO.userError "resume-cost case 26")
  if !(decide ((twoStageQuotaSearchInstrumented 1 (fun _ => 1) 0 0 1 0).2 ≠ streamingStats 1 (fun _ => 1) 0 0 0)) then throw (IO.userError "resume-cost case 27")
  if !(decide (view (resumeQuotaSearchInstrumented (startQuotaSearch 2 half 0 (2/5) 3) 1).1 = some (3, [1/2, 7/8, 1]))) then throw (IO.userError "resume-cost case 28")
  if !(decide (view (resumeQuotaSearchInstrumented (startQuotaSearch 1 (fun _ => 0) 0 0 2) 4).1 = some (4, [0, 1]))) then throw (IO.userError "resume-cost case 29")
  if !(decide ((twoStageQuotaSearchInstrumented 2 half 0 (1/8) 5 6).2 = streamingStats 2 half 0 (1/8) 6)) then throw (IO.userError "resume-cost case 30")
  IO.println "QUOTA_RESUME_COST_OK 30"

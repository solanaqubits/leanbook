/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaChainContract
open CryptoHiddenScalarQuotaChainContract
open CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaMinimumContract

def half : ℕ → ℚ := fun _ => 1/2

def view {n p j ε} (r : QuotaSearchResult n p j ε) : Option (ℕ × List ℚ) :=
  match r with
  | .found _ => none
  | .exhausted c => some (c.bound, c.row.toList)

example : lastCap 3 [] = 3 := by decide +kernel

example : lastCap 0 [0, 3, 3, 4] = 4 := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 0 0 []).2 = (⟨1, 1, 0, 0⟩ : TabularStats)
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 1 0 [0, 2, 4]).1.toOption = some 0
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 1 0 [0, 2, 4]).2 = (⟨1, 1, 0, 0⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [0, 3, 3, 4]).1.toOption = some 4
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [0, 3, 3, 4]).2 = (⟨5, 1, 4, 8⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (2/5) 4 [5, 6]).1.toOption = some 4
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (2/5) 4 [5, 6]).2 = (⟨5, 1, 4, 8⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [2, 4, 6]).1.toOption = some 4
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [2, 4, 6]).2 = (⟨5, 1, 4, 8⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (1/8) 0 [1, 3, 5, 6, 7]).1.toOption = some 6
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (1/8) 0 [1, 3, 5, 6, 7]).2 = (⟨7, 1, 6, 12⟩ :
  TabularStats) := by decide +kernel

example : view (runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 0 [1, 1, 3]).1 = some (3, [0,
  1]) := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 0 [1, 1, 3]).2 = (⟨4, 1, 3, 3⟩ :
  TabularStats) := by decide +kernel

example : view (runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [1, 3]).1 = some (3, [1/2, 7/8,
  1]) := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [1, 3]).2 = (⟨4, 1, 3, 6⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 0 half 0 0 0 [1, 2]).1.toOption = some 0
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 0 half 0 0 0 [1, 2]).2 = (⟨1, 1, 0, 0⟩ : TabularStats)
  := by decide +kernel

example : view (runQuotaResumeChainInstrumented 0 half 0 (-1) 0 [1, 3]).1 = some (3, [1])
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 0 half 0 (-1) 0 [1, 3]).2 = (⟨4, 1, 3, 0⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 3 (-1) 0 [1, 3]).2 = (⟨4, 1, 3, 6⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => 2) 0 (-1) 0 [0, 1, 2]).1.toOption = some 1
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => 2) 0 (-1) 0 [0, 1, 2]).2 = (⟨2, 1, 1, 1⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => -1) 0 0 0 [1, 3]).1.toOption = none
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => -1) 0 0 0 [1, 3]).2 = (⟨4, 1, 3, 3⟩ :
  TabularStats) := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => 1) 0 0 1 [0]).1.toOption ≠
  chooseQuotaBudgetWithin 1 (fun _ => 1) 0 0 0 := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => 1) 0 0 1 [0]).2 ≠ streamingStats 1 (fun _ =>
  1) 0 0 0 := by decide +kernel

example : view (runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 3 [1]).1 = some (3, [0, 1])
  := by decide +kernel

example : (runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 3 [1]).2 ≠ streamingStats 1 (fun _ =>
  0) 0 0 1 := by decide +kernel

example : (runQuotaResumeChainInstrumented 2 half 0 (1/8) 0 [2, 4, 6]).2 = streamingStats 2 half 0
  (1/8) 6 := by decide +kernel

example : ¬ List.IsChain (· ≤ ·) ([1, 0] : List ℕ) := by decide +kernel

example {n p j ε} (c d : QuotaSearchCursor n p j ε) (h : c.bound = d.bound) :
    c = d := cursor_ext c d h
example (n p j ε a b) (h : a ≤ b) :
    resumeQuotaSearch (startQuotaSearch n p j ε a) b = startQuotaSearch n p j ε b :=
  resumeQuotaSearch_startQuotaSearch n p j ε a b h
example (n p j ε a cs) (h : List.IsChain (· ≤ ·) (a :: cs)) :
    runQuotaResumeChainInstrumented n p j ε a cs =
      (startQuotaSearch n p j ε (lastCap a cs), streamingStats n p j ε (lastCap a cs)) :=
  chain_pair_eq n p j ε a cs h
example (n p j ε a cs) (h : List.IsChain (· ≤ ·) (a :: cs)) :
    (runQuotaResumeChainInstrumented n p j ε a cs).1.toOption =
      chooseQuotaBudgetWithin n p j ε (lastCap a cs) := chain_toOption n p j ε a cs h

def main : IO Unit := do
  if !(decide (lastCap 3 [] = 3)) then throw (IO.userError "chain case 1")
  if !(decide (lastCap 0 [0, 3, 3, 4] = 4)) then throw (IO.userError "chain case 2")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 0 0 []).2 = (⟨1, 1, 0, 0⟩ :
    TabularStats))) then throw (IO.userError "chain case 3")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 1 0 [0, 2, 4]).1.toOption = some 0)) then
    throw (IO.userError "chain case 4")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 1 0 [0, 2, 4]).2 = (⟨1, 1, 0, 0⟩ :
    TabularStats))) then throw (IO.userError "chain case 5")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [0, 3, 3, 4]).1.toOption = some
    4)) then throw (IO.userError "chain case 6")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [0, 3, 3, 4]).2 = (⟨5, 1, 4, 8⟩ :
    TabularStats))) then throw (IO.userError "chain case 7")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (2/5) 4 [5, 6]).1.toOption = some 4)) then
    throw (IO.userError "chain case 8")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (2/5) 4 [5, 6]).2 = (⟨5, 1, 4, 8⟩ :
    TabularStats))) then throw (IO.userError "chain case 9")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [2, 4, 6]).1.toOption = some 4))
    then throw (IO.userError "chain case 10")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [2, 4, 6]).2 = (⟨5, 1, 4, 8⟩ :
    TabularStats))) then throw (IO.userError "chain case 11")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (1/8) 0 [1, 3, 5, 6, 7]).1.toOption = some
    6)) then throw (IO.userError "chain case 12")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (1/8) 0 [1, 3, 5, 6, 7]).2 = (⟨7, 1, 6,
    12⟩ : TabularStats))) then throw (IO.userError "chain case 13")
  if !(decide (view (runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 0 [1, 1, 3]).1 = some (3,
    [0, 1]))) then throw (IO.userError "chain case 14")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 0 [1, 1, 3]).2 = (⟨4, 1, 3, 3⟩ :
    TabularStats))) then throw (IO.userError "chain case 15")
  if !(decide (view (runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [1, 3]).1 = some (3, [1/2,
    7/8, 1]))) then throw (IO.userError "chain case 16")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (2/5) 0 [1, 3]).2 = (⟨4, 1, 3, 6⟩ :
    TabularStats))) then throw (IO.userError "chain case 17")
  if !(decide ((runQuotaResumeChainInstrumented 0 half 0 0 0 [1, 2]).1.toOption = some 0)) then
    throw (IO.userError "chain case 18")
  if !(decide ((runQuotaResumeChainInstrumented 0 half 0 0 0 [1, 2]).2 = (⟨1, 1, 0, 0⟩ :
    TabularStats))) then throw (IO.userError "chain case 19")
  if !(decide (view (runQuotaResumeChainInstrumented 0 half 0 (-1) 0 [1, 3]).1 = some (3, [1])))
    then throw (IO.userError "chain case 20")
  if !(decide ((runQuotaResumeChainInstrumented 0 half 0 (-1) 0 [1, 3]).2 = (⟨4, 1, 3, 0⟩ :
    TabularStats))) then throw (IO.userError "chain case 21")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 3 (-1) 0 [1, 3]).2 = (⟨4, 1, 3, 6⟩ :
    TabularStats))) then throw (IO.userError "chain case 22")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => 2) 0 (-1) 0 [0, 1, 2]).1.toOption =
    some 1)) then throw (IO.userError "chain case 23")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => 2) 0 (-1) 0 [0, 1, 2]).2 = (⟨2, 1, 1,
    1⟩ : TabularStats))) then throw (IO.userError "chain case 24")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => -1) 0 0 0 [1, 3]).1.toOption = none))
    then throw (IO.userError "chain case 25")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => -1) 0 0 0 [1, 3]).2 = (⟨4, 1, 3, 3⟩ :
    TabularStats))) then throw (IO.userError "chain case 26")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => 1) 0 0 1 [0]).1.toOption ≠
    chooseQuotaBudgetWithin 1 (fun _ => 1) 0 0 0)) then throw (IO.userError "chain case 27")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => 1) 0 0 1 [0]).2 ≠ streamingStats 1 (fun
    _ => 1) 0 0 0)) then throw (IO.userError "chain case 28")
  if !(decide (view (runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 3 [1]).1 = some (3, [0,
    1]))) then throw (IO.userError "chain case 29")
  if !(decide ((runQuotaResumeChainInstrumented 1 (fun _ => 0) 0 0 3 [1]).2 ≠ streamingStats 1 (fun
    _ => 0) 0 0 1)) then throw (IO.userError "chain case 30")
  if !(decide ((runQuotaResumeChainInstrumented 2 half 0 (1/8) 0 [2, 4, 6]).2 = streamingStats 2
    half 0 (1/8) 6)) then throw (IO.userError "chain case 31")
  if !(decide (¬ List.IsChain (· ≤ ·) ([1, 0] : List ℕ))) then throw (IO.userError "chain case 32")
  IO.println "QUOTA_CHAIN_OK 32"

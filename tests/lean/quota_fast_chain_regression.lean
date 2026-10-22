import Verification.CryptoHiddenScalarQuotaFastChainContract
open CryptoHiddenScalarQuotaFastChainContract
open CryptoHiddenScalarQuotaFastStartContract
open CryptoHiddenScalarQuotaChainContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaMinimumContract

def view {n p j ε} (r : QuotaSearchResult n p j ε) : Option ℕ × Option (ℕ × List ℚ) :=
  match r with
  | .found t => (some t, none)
  | .exhausted c => (none, some (c.bound, c.row.toList))

example : view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 []).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 []).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 []).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 []).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 []).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 []).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 [0, 1, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 [0, 1, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 [0, 1, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 [0, 1, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 [0, 1, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 [0, 1, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 2 [2, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 2 [2, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 2 [2, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 2 [2, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 2 [2, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 2 [2, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 []).1 = (none, some (0, [(1)])) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 []).2 = (⟨2, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 []).1 = (none, some (0, [(0), (0), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 []).2 = (⟨2, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 3]).1 = (none, some (3, [(1)])) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 3]).2 = (⟨5, 1, 3, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 [0, 1, 3]).1 = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 [0, 1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 1 [1, 3]).1 = (none, some (3, [(1)])) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 1 [1, 3]).2 = (⟨5, 1, 3, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 1 [1, 3]).1 = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 1 [1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (0) 0 []).1 = (none, some (0, [(0), (0), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (0) 0 []).2 = (⟨2, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [0, 3, 3, 4]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [0, 3, 3, 4]).2 = (⟨6, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4 [4, 5, 6]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4 [4, 5, 6]).2 = (⟨6, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [2, 4, 6]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [2, 4, 6]).2 = (⟨6, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 0 [1, 3, 5, 6, 7]).1 = (some 6, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 0 [1, 3, 5, 6, 7]).2 = (⟨8, 1, 6, 12⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [1, 3]).1 = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 2 [3, 5]).1 = (none, some (5, [(13/16), (31/32), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 2 [3, 5]).2 = (⟨7, 1, 5, 10⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 2]).1 = (some 1, none) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 2]).2 = (⟨3, 1, 1, 1⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).1 = (none, some (3, [(-7), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).2 = (⟨5, 1, 3, 3⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 0 [1, 2, 4]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 0 [1, 2, 4]).2 = (⟨6, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 2]).1 = (some 2, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 2]).2 = (⟨4, 1, 2, 4⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).1 = (none, some (3, [(0), (1), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(1)] : List ℚ).getD i 0) 0 (0) 1 [0]).1 = (some 1, none) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(1)] : List ℚ).getD i 0) 0 (0) 1 [0]).2 = (⟨3, 1, 1, 1⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) 3 [1]).1 = (none, some (3, [(0), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) 3 [1]).2 = (⟨5, 1, 3, 3⟩ : TabularStats) := by decide +kernel

example : view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3 [0]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3 [0]).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example (n p j ε a cs) (h : List.IsChain (· ≤ ·) (a :: cs)) :
    runQuotaResumeChainFastInstrumented n p j ε a cs =
      startQuotaSearchFastInstrumented n p j ε (lastCap a cs) := fast_chain_pair_eq n p j ε a cs h
example (n p j ε a cs) (h : List.IsChain (· ≤ ·) (a :: cs)) :
    (runQuotaResumeChainFastInstrumented n p j ε a cs).1 =
      startQuotaSearch n p j ε (lastCap a cs) := fast_chain_result n p j ε a cs h
example (n p j ε a cs) (h : List.IsChain (· ≤ ·) (a :: cs)) :
    (runQuotaResumeChainFastInstrumented n p j ε a cs).1.toOption =
      chooseQuotaBudgetWithin n p j ε (lastCap a cs) := fast_chain_toOption n p j ε a cs h
example : (runQuotaResumeChainFastInstrumented 1 (fun _ => 1) 0 0 1 [0]).1.toOption ≠
    chooseQuotaBudgetWithin 1 (fun _ => 1) 0 0 0 := by decide +kernel
example : (runQuotaResumeChainFastInstrumented 1 (fun _ => 0) 0 0 3 [1]).2 ≠
    (startQuotaSearchFastInstrumented 1 (fun _ => 0) 0 0 1).2 := by decide +kernel
example : ¬ List.IsChain (· ≤ ·) ([1, 0] : List ℕ) := by decide +kernel
example : (runQuotaResumeChainFastInstrumented 2 (fun _ => 1/2) 0 (2/5) 0 [0,1,2,3,4,5]).2.checks =
    (runQuotaResumeChainInstrumented 2 (fun _ => 1/2) 0 (2/5) 0 [0,1,2,3,4,5]).2.checks + 1 := by decide +kernel

def main : IO Unit := do
  if !(decide (view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 []).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 []).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 1")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 []).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 []).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 2")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 []).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 []).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 3")
  if !(decide (view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 [0, 1, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0 [0, 1, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 4")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 [0, 1, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0 [0, 1, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 5")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 [0, 1, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0 [0, 1, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 6")
  if !(decide (view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 2 [2, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 2 [2, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 7")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 2 [2, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 2 [2, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 8")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 2 [2, 3]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 2 [2, 3]).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 9")
  if !(decide (view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 []).1 = (none, some (0, [(1)])) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 []).2 = (⟨2, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 10")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 []).1 = (none, some (0, [(0), (0), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 []).2 = (⟨2, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 11")
  if !(decide (view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 3]).1 = (none, some (3, [(1)])) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 3]).2 = (⟨5, 1, 3, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 12")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 [0, 1, 3]).1 = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 0 [0, 1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast chain case 13")
  if !(decide (view (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 1 [1, 3]).1 = (none, some (3, [(1)])) ∧
    (runQuotaResumeChainFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 1 [1, 3]).2 = (⟨5, 1, 3, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 14")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 1 [1, 3]).1 = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 3 (-1) 1 [1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast chain case 15")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (0) 0 []).1 = (none, some (0, [(0), (0), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (0) 0 []).2 = (⟨2, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 16")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [0, 3, 3, 4]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [0, 3, 3, 4]).2 = (⟨6, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "fast chain case 17")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4 [4, 5, 6]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4 [4, 5, 6]).2 = (⟨6, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "fast chain case 18")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [2, 4, 6]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [2, 4, 6]).2 = (⟨6, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "fast chain case 19")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 0 [1, 3, 5, 6, 7]).1 = (some 6, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 0 [1, 3, 5, 6, 7]).2 = (⟨8, 1, 6, 12⟩ : TabularStats))) then throw (IO.userError "fast chain case 20")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [1, 3]).1 = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 0 [1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast chain case 21")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 2 [3, 5]).1 = (none, some (5, [(13/16), (31/32), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 2 [3, 5]).2 = (⟨7, 1, 5, 10⟩ : TabularStats))) then throw (IO.userError "fast chain case 22")
  if !(decide (view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 2]).1 = (some 1, none) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 0 [0, 1, 2]).2 = (⟨3, 1, 1, 1⟩ : TabularStats))) then throw (IO.userError "fast chain case 23")
  if !(decide (view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).1 = (none, some (3, [(-7), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).2 = (⟨5, 1, 3, 3⟩ : TabularStats))) then throw (IO.userError "fast chain case 24")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 0 [1, 2, 4]).1 = (some 4, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 0 [1, 2, 4]).2 = (⟨6, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "fast chain case 25")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 2]).1 = (some 2, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 2]).2 = (⟨4, 1, 2, 4⟩ : TabularStats))) then throw (IO.userError "fast chain case 26")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).1 = (none, some (3, [(0), (1), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 0 [1, 3]).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast chain case 27")
  if !(decide (view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(1)] : List ℚ).getD i 0) 0 (0) 1 [0]).1 = (some 1, none) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(1)] : List ℚ).getD i 0) 0 (0) 1 [0]).2 = (⟨3, 1, 1, 1⟩ : TabularStats))) then throw (IO.userError "fast chain case 28")
  if !(decide (view (runQuotaResumeChainFastInstrumented 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) 3 [1]).1 = (none, some (3, [(0), (1)])) ∧
    (runQuotaResumeChainFastInstrumented 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) 3 [1]).2 = (⟨5, 1, 3, 3⟩ : TabularStats))) then throw (IO.userError "fast chain case 29")
  if !(decide (view (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3 [0]).1 = (some 0, none) ∧
    (runQuotaResumeChainFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3 [0]).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast chain case 30")
  IO.println "QUOTA_FAST_CHAIN_OK 30"

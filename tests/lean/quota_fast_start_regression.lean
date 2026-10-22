import Verification.CryptoHiddenScalarQuotaFastStartContract
open CryptoHiddenScalarQuotaFastStartContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaComparisonContract

def view {n p j ε} (r : QuotaSearchResult n p j ε) : Option ℕ × Option (ℕ × List ℚ) :=
  match r with
  | .found t => (some t, none)
  | .exhausted c => (none, some (c.bound, c.row.toList))

example : view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0) = (none, some (0, [(1)])) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0).2 = (⟨2, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 0) = (none, some (0, [(0), (0), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 0).2 = (⟨2, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 3) = (none, some (3, [(1)])) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 3).2 = (⟨5, 1, 3, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 3) = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (0) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (0) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (-1) 3) = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (-1) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 3) = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4) = (some 4, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4).2 = (⟨6, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 5) = (none, some (5, [(13/16), (31/32), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 5).2 = (⟨7, 1, 5, 10⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 6) = (some 6, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 6).2 = (⟨8, 1, 6, 12⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 2) = (some 1, none) ∧
    (startQuotaSearchFastInstrumented 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 2).2 = (⟨3, 1, 1, 1⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 3) = (none, some (3, [(-7), (1)])) ∧
    (startQuotaSearchFastInstrumented 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 3).2 = (⟨5, 1, 3, 3⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 4) = (some 4, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 4).2 = (⟨6, 1, 4, 8⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 2) = (some 2, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 2).2 = (⟨4, 1, 2, 4⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 3) = (none, some (3, [(0), (1), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats) := by decide +kernel

example : view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (-1) 0) = (none, some (0, [(0), (0), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (-1) 0).2 = (⟨2, 1, 0, 0⟩ : TabularStats) := by decide +kernel

example (n p j ε cap) : startQuotaSearchFast n p j ε cap = startQuotaSearch n p j ε cap :=
  startQuotaSearchFast_eq n p j ε cap
example (n p j ε cap) : (startQuotaSearchFastInstrumented n p j ε cap).1 =
    startQuotaSearchFast n p j ε cap := startQuotaSearchFastInstrumented_result n p j ε cap
example (n p j ε cap) (h : (n ≤ j ∧ ε < 0) ∨ (j < n ∧ ε < 1)) :
    (startQuotaSearchFastInstrumented n p j ε cap).2.checks =
      (startQuotaSearchInstrumented n p j ε cap).2.checks + 1 := by
  rw [fast_delegates n p j ε cap h]
example : (startQuotaSearchFastInstrumented 2 (fun _ => 1/2) 2 (-1) 3).2.checks ≠
    (startQuotaSearchInstrumented 2 (fun _ => 1/2) 2 (-1) 3).2.checks := by decide +kernel
-- Absorption at the queried index does not make the full retained row constant.
example : view (startQuotaSearchFast 2 (fun _ => 1/2) 2 (-1) 0) ≠
    view (startQuotaSearchFast 2 (fun _ => 1/2) 2 (-1) 3) := by decide +kernel

def main : IO Unit := do
  if !(decide (view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 1")
  if !(decide (view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0) = (none, some (0, [(1)])) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 0).2 = (⟨2, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 2")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 3")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 0) = (none, some (0, [(0), (0), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 0).2 = (⟨2, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 4")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 5")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 0) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 0).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 6")
  if !(decide (view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 7")
  if !(decide (view (startQuotaSearchFast 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 3) = (none, some (3, [(1)])) ∧
    (startQuotaSearchFastInstrumented 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) 3).2 = (⟨5, 1, 3, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 8")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (0) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 9")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 3) = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 2 (-1) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast start case 10")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 11")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 12")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (0) 3) = (some 0, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (0) 3).2 = (⟨1, 0, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 13")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (-1) 3) = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 4 (-1) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast start case 14")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 3) = (none, some (3, [(1/2), (7/8), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast start case 15")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4) = (some 4, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) 4).2 = (⟨6, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "fast start case 16")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 5) = (none, some (5, [(13/16), (31/32), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 5).2 = (⟨7, 1, 5, 10⟩ : TabularStats))) then throw (IO.userError "fast start case 17")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 6) = (some 6, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) 6).2 = (⟨8, 1, 6, 12⟩ : TabularStats))) then throw (IO.userError "fast start case 18")
  if !(decide (view (startQuotaSearchFast 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 2) = (some 1, none) ∧
    (startQuotaSearchFastInstrumented 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) 2).2 = (⟨3, 1, 1, 1⟩ : TabularStats))) then throw (IO.userError "fast start case 19")
  if !(decide (view (startQuotaSearchFast 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 3) = (none, some (3, [(-7), (1)])) ∧
    (startQuotaSearchFastInstrumented 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) 3).2 = (⟨5, 1, 3, 3⟩ : TabularStats))) then throw (IO.userError "fast start case 20")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 4) = (some 4, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) 4).2 = (⟨6, 1, 4, 8⟩ : TabularStats))) then throw (IO.userError "fast start case 21")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 2) = (some 2, none) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1), (1)] : List ℚ).getD i 0) 0 (0) 2).2 = (⟨4, 1, 2, 4⟩ : TabularStats))) then throw (IO.userError "fast start case 22")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 3) = (none, some (3, [(0), (1), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(0), (1)] : List ℚ).getD i 0) 0 (0) 3).2 = (⟨5, 1, 3, 6⟩ : TabularStats))) then throw (IO.userError "fast start case 23")
  if !(decide (view (startQuotaSearchFast 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (-1) 0) = (none, some (0, [(0), (0), (1)])) ∧
    (startQuotaSearchFastInstrumented 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (-1) 0).2 = (⟨2, 1, 0, 0⟩ : TabularStats))) then throw (IO.userError "fast start case 24")
  IO.println "QUOTA_FAST_START_OK 24"

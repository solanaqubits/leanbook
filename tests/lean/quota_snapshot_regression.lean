import Verification.CryptoHiddenScalarQuotaSnapshotContract
open CryptoHiddenScalarQuotaSnapshotContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaTabularContract

def restoredView (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (s : QuotaCursorSnapshot) :
    Option QuotaCursorSnapshot := (restoreCursor? n p j ε s).map snapshotCursor

def resumedView (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (s : QuotaCursorSnapshot)
    (cap : ℕ) : Option (Option ℕ × Option QuotaCursorSnapshot) :=
  (restoreCursor? n p j ε s).map fun c =>
    match resumeQuotaSearch (.exhausted c) cap with
    | .found t => (some t, none)
    | .exhausted d => (none, some (snapshotCursor d))

-- n0-failed
example : restoredView 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) (⟨0, [(1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) (⟨0, [(1)]⟩ : QuotaCursorSnapshot) 3 = some (none, some (⟨3, [(1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

-- n0-found
example : restoredView 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) (⟨0, [(1)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- zero-bound
example : restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) 4 = some (none, some (⟨4, [(11/16), (15/16), (1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

-- before-four
example : restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) 4 = some (some 4, none) := by decide +kernel

-- before-six
example : restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨5, [(13/16), (31/32), (1)]⟩ : QuotaCursorSnapshot) = some (⟨5, [(13/16), (31/32), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨5, [(13/16), (31/32), (1)]⟩ : QuotaCursorSnapshot) 6 = some (some 6, none) := by decide +kernel

-- equal-bound
example : restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) 3 = some (none, some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

-- smaller-bound
example : restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) 1 = some (none, some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

-- length-short
example : restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- length-long
example : restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0), (1), (0)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- active-mutation
example : restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(1), (1)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- absorbed-mutation
example : restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0), (0)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- early-found-final-failure
example : restoredView 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0), (1)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- negative-profile
example : restoredView 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) (⟨3, [(-7), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(-7), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) (⟨3, [(-7), (1)]⟩ : QuotaCursorSnapshot) 4 = some (none, some (⟨4, [(-15), (1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

-- above-one-before-success
example : restoredView 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) 1 = some (some 1, none) := by decide +kernel

-- absorbed-negative-epsilon
example : restoredView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 3 (-1) (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) = some (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 3 (-1) (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) 5 = some (none, some (⟨5, [(31/32), (1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

-- absorbed-nonnegative-epsilon
example : restoredView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 3 (0) (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- constant-row-new-bound
example : restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) 2 = some (none, some (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

-- changed-context-valid
example : restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (1/2) (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) := by decide +kernel

-- changed-context-invalid
example : restoredView 1 (fun i => ([(1)] : List ℚ).getD i 0) 0 (0) (⟨3, [(0), (1)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- nonuniform
example : restoredView 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) (⟨3, [(13/36), (19/27), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(13/36), (19/27), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) (⟨3, [(13/36), (19/27), (1)]⟩ : QuotaCursorSnapshot) 4 = some (some 4, none) := by decide +kernel

-- found-at-zero
example : restoredView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 0 (1) (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) = none := by decide +kernel

-- valid-outside-probability
example : restoredView 2 (fun i => ([(-1), (2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(-1), (2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) 2 = some (none, some (⟨2, [(-2), (0), (1)]⟩ : QuotaCursorSnapshot)) := by decide +kernel

example : (quotaRow 1 (fun _ => 2) 2).toList = [0, 1] ∧
    (0 : ℚ) < quotaDeficit 1 (fun _ => 2) 2 0 ∧
    quotaDeficit 1 (fun _ => 2) 1 0 ≤ 0 ∧
    restoredView 1 (fun _ => 2) 0 0 ⟨2, [0, 1]⟩ = none := by decide +kernel

example {n p j ε} (c : QuotaSearchCursor n p j ε) :
    restoreCursor? n p j ε (snapshotCursor c) = some c := restore_snapshot c

example {n p j ε} (s : QuotaCursorSnapshot) (c : QuotaSearchCursor n p j ε)
    (h : restoreCursor? n p j ε s = some c) :
    ∀ t ≤ s.bound, ε < quotaDeficit n p t j := (restore_sound s c h).1.2.2

def main : IO Unit := do
  if !(decide (restoredView 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) (⟨0, [(1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 0 (fun i => ([] : List ℚ).getD i 0) 0 (-1) (⟨0, [(1)]⟩ : QuotaCursorSnapshot) 3 = some (none, some (⟨3, [(1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 1")
  if !(decide (restoredView 0 (fun i => ([] : List ℚ).getD i 0) 0 (0) (⟨0, [(1)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 2")
  if !(decide (restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) 4 = some (none, some (⟨4, [(11/16), (15/16), (1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 3")
  if !(decide (restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (2/5) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) 4 = some (some 4, none))) then throw (IO.userError "snapshot case 4")
  if !(decide (restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨5, [(13/16), (31/32), (1)]⟩ : QuotaCursorSnapshot) = some (⟨5, [(13/16), (31/32), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨5, [(13/16), (31/32), (1)]⟩ : QuotaCursorSnapshot) 6 = some (some 6, none))) then throw (IO.userError "snapshot case 5")
  if !(decide (restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) 3 = some (none, some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 6")
  if !(decide (restoredView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/2)] : List ℚ).getD i 0) 0 (1/8) (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot) 1 = some (none, some (⟨3, [(1/2), (7/8), (1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 7")
  if !(decide (restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 8")
  if !(decide (restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0), (1), (0)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 9")
  if !(decide (restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(1), (1)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 10")
  if !(decide (restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0), (0)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 11")
  if !(decide (restoredView 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (0) (⟨2, [(0), (1)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 12")
  if !(decide (restoredView 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) (⟨3, [(-7), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(-7), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(-1)] : List ℚ).getD i 0) 0 (0) (⟨3, [(-7), (1)]⟩ : QuotaCursorSnapshot) 4 = some (none, some (⟨4, [(-15), (1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 13")
  if !(decide (restoredView 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) 1 = some (some 1, none))) then throw (IO.userError "snapshot case 14")
  if !(decide (restoredView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 3 (-1) (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) = some (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 3 (-1) (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) 5 = some (none, some (⟨5, [(31/32), (1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 15")
  if !(decide (restoredView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 3 (0) (⟨2, [(3/4), (1)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 16")
  if !(decide (restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (0) (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) 2 = some (none, some (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 17")
  if !(decide (restoredView 1 (fun i => ([(0)] : List ℚ).getD i 0) 0 (1/2) (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨7, [(0), (1)]⟩ : QuotaCursorSnapshot))) then throw (IO.userError "snapshot case 18")
  if !(decide (restoredView 1 (fun i => ([(1)] : List ℚ).getD i 0) 0 (0) (⟨3, [(0), (1)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 19")
  if !(decide (restoredView 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) (⟨3, [(13/36), (19/27), (1)]⟩ : QuotaCursorSnapshot) = some (⟨3, [(13/36), (19/27), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(1/2), (1/3)] : List ℚ).getD i 0) 0 (1/2) (⟨3, [(13/36), (19/27), (1)]⟩ : QuotaCursorSnapshot) 4 = some (some 4, none))) then throw (IO.userError "snapshot case 20")
  if !(decide (restoredView 1 (fun i => ([(1/2)] : List ℚ).getD i 0) 0 (1) (⟨0, [(0), (1)]⟩ : QuotaCursorSnapshot) = none)) then throw (IO.userError "snapshot case 21")
  if !(decide (restoredView 2 (fun i => ([(-1), (2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) = some (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) ∧ resumedView 2 (fun i => ([(-1), (2)] : List ℚ).getD i 0) 0 (-1) (⟨0, [(0), (0), (1)]⟩ : QuotaCursorSnapshot) 2 = some (none, some (⟨2, [(-2), (0), (1)]⟩ : QuotaCursorSnapshot)))) then throw (IO.userError "snapshot case 22")
  IO.println "QUOTA_SNAPSHOT_OK 22"

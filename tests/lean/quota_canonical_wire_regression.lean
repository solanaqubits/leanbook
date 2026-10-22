import Verification.CryptoHiddenScalarQuotaCanonicalWireContract
open CryptoHiddenScalarQuotaCanonicalWireContract
open CryptoHiddenScalarQuotaSnapshotContract
open CryptoHiddenScalarQuotaResumableContract

def resumedView (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (w : QuotaSnapshotWire) (cap : ℕ) :
    Option (Option ℕ × Option QuotaCursorSnapshot) :=
  (restoreFromExternal? n p j ε w).map fun c =>
    match resumeQuotaSearch (.exhausted c) cap with
    | .found t => (some t, none)
    | .exhausted d => (none, some (snapshotCursor d))

-- rat-0-1
example : decodeRatCanonical? ⟨0, 1⟩ = some (0 / 1 : ℚ) := by decide +kernel

-- rat-1-1
example : decodeRatCanonical? ⟨1, 1⟩ = some (1 / 1 : ℚ) := by decide +kernel

-- rat--1-1
example : decodeRatCanonical? ⟨-1, 1⟩ = some (-1 / 1 : ℚ) := by decide +kernel

-- rat-1-2
example : decodeRatCanonical? ⟨1, 2⟩ = some (1 / 2 : ℚ) := by decide +kernel

-- rat--1-2
example : decodeRatCanonical? ⟨-1, 2⟩ = some (-1 / 2 : ℚ) := by decide +kernel

-- rat-17-31
example : decodeRatCanonical? ⟨17, 31⟩ = some (17 / 31 : ℚ) := by decide +kernel

-- rat-123456789012345678901-2
example : decodeRatCanonical? ⟨123456789012345678901, 2⟩ = some (123456789012345678901 / 2 : ℚ) := by decide +kernel

-- rat-2-4
example : decodeRatCanonical? ⟨2, 4⟩ = none := by decide +kernel

-- rat--2-4
example : decodeRatCanonical? ⟨-2, 4⟩ = none := by decide +kernel

-- rat-0-2
example : decodeRatCanonical? ⟨0, 2⟩ = none := by decide +kernel

-- rat-0-0
example : decodeRatCanonical? ⟨0, 0⟩ = none := by decide +kernel

-- rat-1-0
example : decodeRatCanonical? ⟨1, 0⟩ = none := by decide +kernel

-- rat--1-0
example : decodeRatCanonical? ⟨-1, 0⟩ = none := by decide +kernel

-- rat-6-9
example : decodeRatCanonical? ⟨6, 9⟩ = none := by decide +kernel

-- empty
example : decodeSnapshotCanonical? ⟨99, []⟩ = some ⟨99, []⟩ := by decide +kernel

-- ordered
example : decodeSnapshotCanonical? ⟨7, [⟨-1, 2⟩, ⟨0, 1⟩, ⟨3, 4⟩]⟩ = some ⟨7, [-1/2, 0, 3/4]⟩ := by decide +kernel

-- bad-head
example : decodeSnapshotCanonical? ⟨0, [⟨2, 4⟩, ⟨1, 1⟩]⟩ = none := by decide +kernel

-- bad-middle
example : decodeSnapshotCanonical? ⟨0, [⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩]⟩ = none := by decide +kernel

-- bad-tail
example : decodeSnapshotCanonical? ⟨0, [⟨1, 1⟩, ⟨1, 0⟩]⟩ = none := by decide +kernel

-- canonical-but-invalid-length
example : decodeSnapshotCanonical? ⟨3, []⟩ = some ⟨3, []⟩ ∧ (restoreFromExternal? 1 (fun _ => 0) 0 0 ⟨3, []⟩).isNone = true := by decide +kernel

-- canonical-but-invalid-row
example : (restoreFromExternal? 1 (fun _ => 0) 0 0 ⟨3, [⟨1, 1⟩, ⟨1, 1⟩]⟩).isNone = true := by decide +kernel

-- earlier-success-final-failure
example : (restoreFromExternal? 1 (fun _ => 2) 0 0 ⟨2, [⟨0, 1⟩, ⟨1, 1⟩]⟩).isNone = true := by decide +kernel

-- four
example : resumedView 2 (fun _ => 1/2) 0 (2/5) ⟨3, [⟨1, 2⟩, ⟨7, 8⟩, ⟨1, 1⟩]⟩ 4 = some (some 4, none) := by decide +kernel

-- six
example : resumedView 2 (fun _ => 1/2) 0 (1/8) ⟨5, [⟨13, 16⟩, ⟨31, 32⟩, ⟨1, 1⟩]⟩ 6 = some (some 6, none) := by decide +kernel

-- negative-tolerance
example : resumedView 1 (fun _ => 2) 0 (-1) ⟨0, [⟨0, 1⟩, ⟨1, 1⟩]⟩ 1 = some (some 1, none) := by decide +kernel

-- negative-profile
example : resumedView 1 (fun _ => -1) 0 0 ⟨3, [⟨-7, 1⟩, ⟨1, 1⟩]⟩ 4 = some (none, some ⟨4, [-15, 1]⟩) := by decide +kernel

-- smaller-window
example : resumedView 1 (fun _ => 0) 0 0 ⟨7, [⟨0, 1⟩, ⟨1, 1⟩]⟩ 2 = some (none, some ⟨7, [0, 1]⟩) := by decide +kernel

-- absorbed-failure
example : resumedView 0 (fun _ => 0) 0 (-1) ⟨0, [⟨1, 1⟩]⟩ 3 = some (none, some ⟨3, [1]⟩) := by decide +kernel

-- absorbed-success-rejected
example : (restoreFromExternal? 0 (fun _ => 0) 0 0 ⟨0, [⟨1, 1⟩]⟩).isNone = true := by decide +kernel

example (q : ℚ) : decodeRatCanonical? (encodeRatCanonical q) = some q := decode_encode_rat q
example (w : QuotaSnapshotWire) (s : QuotaCursorSnapshot) :
    decodeSnapshotCanonical? w = some s ↔ encodeSnapshotCanonical s = w := decode_snapshot_iff w s
example {n p j ε} (c : QuotaSearchCursor n p j ε) :
    restoreFromExternal? n p j ε (encodeSnapshotCanonical (snapshotCursor c)) = some c :=
  restore_encoded_cursor c

def main : IO Unit := do
  if !(decide (decodeRatCanonical? ⟨0, 1⟩ = some (0 / 1 : ℚ))) then throw (IO.userError "rat-0-1")
  if !(decide (decodeRatCanonical? ⟨1, 1⟩ = some (1 / 1 : ℚ))) then throw (IO.userError "rat-1-1")
  if !(decide (decodeRatCanonical? ⟨-1, 1⟩ = some (-1 / 1 : ℚ))) then throw (IO.userError "rat--1-1")
  if !(decide (decodeRatCanonical? ⟨1, 2⟩ = some (1 / 2 : ℚ))) then throw (IO.userError "rat-1-2")
  if !(decide (decodeRatCanonical? ⟨-1, 2⟩ = some (-1 / 2 : ℚ))) then throw (IO.userError "rat--1-2")
  if !(decide (decodeRatCanonical? ⟨17, 31⟩ = some (17 / 31 : ℚ))) then throw (IO.userError "rat-17-31")
  if !(decide (decodeRatCanonical? ⟨123456789012345678901, 2⟩ = some (123456789012345678901 / 2 : ℚ))) then throw (IO.userError "rat-123456789012345678901-2")
  if !(decide (decodeRatCanonical? ⟨2, 4⟩ = none)) then throw (IO.userError "rat-2-4")
  if !(decide (decodeRatCanonical? ⟨-2, 4⟩ = none)) then throw (IO.userError "rat--2-4")
  if !(decide (decodeRatCanonical? ⟨0, 2⟩ = none)) then throw (IO.userError "rat-0-2")
  if !(decide (decodeRatCanonical? ⟨0, 0⟩ = none)) then throw (IO.userError "rat-0-0")
  if !(decide (decodeRatCanonical? ⟨1, 0⟩ = none)) then throw (IO.userError "rat-1-0")
  if !(decide (decodeRatCanonical? ⟨-1, 0⟩ = none)) then throw (IO.userError "rat--1-0")
  if !(decide (decodeRatCanonical? ⟨6, 9⟩ = none)) then throw (IO.userError "rat-6-9")
  if !(decide (decodeSnapshotCanonical? ⟨99, []⟩ = some ⟨99, []⟩)) then throw (IO.userError "empty")
  if !(decide (decodeSnapshotCanonical? ⟨7, [⟨-1, 2⟩, ⟨0, 1⟩, ⟨3, 4⟩]⟩ = some ⟨7, [-1/2, 0, 3/4]⟩)) then throw (IO.userError "ordered")
  if !(decide (decodeSnapshotCanonical? ⟨0, [⟨2, 4⟩, ⟨1, 1⟩]⟩ = none)) then throw (IO.userError "bad-head")
  if !(decide (decodeSnapshotCanonical? ⟨0, [⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩]⟩ = none)) then throw (IO.userError "bad-middle")
  if !(decide (decodeSnapshotCanonical? ⟨0, [⟨1, 1⟩, ⟨1, 0⟩]⟩ = none)) then throw (IO.userError "bad-tail")
  if !(decide (decodeSnapshotCanonical? ⟨3, []⟩ = some ⟨3, []⟩ ∧ (restoreFromExternal? 1 (fun _ => 0) 0 0 ⟨3, []⟩).isNone = true)) then throw (IO.userError "canonical-but-invalid-length")
  if !(decide ((restoreFromExternal? 1 (fun _ => 0) 0 0 ⟨3, [⟨1, 1⟩, ⟨1, 1⟩]⟩).isNone = true)) then throw (IO.userError "canonical-but-invalid-row")
  if !(decide ((restoreFromExternal? 1 (fun _ => 2) 0 0 ⟨2, [⟨0, 1⟩, ⟨1, 1⟩]⟩).isNone = true)) then throw (IO.userError "earlier-success-final-failure")
  if !(decide (resumedView 2 (fun _ => 1/2) 0 (2/5) ⟨3, [⟨1, 2⟩, ⟨7, 8⟩, ⟨1, 1⟩]⟩ 4 = some (some 4, none))) then throw (IO.userError "four")
  if !(decide (resumedView 2 (fun _ => 1/2) 0 (1/8) ⟨5, [⟨13, 16⟩, ⟨31, 32⟩, ⟨1, 1⟩]⟩ 6 = some (some 6, none))) then throw (IO.userError "six")
  if !(decide (resumedView 1 (fun _ => 2) 0 (-1) ⟨0, [⟨0, 1⟩, ⟨1, 1⟩]⟩ 1 = some (some 1, none))) then throw (IO.userError "negative-tolerance")
  if !(decide (resumedView 1 (fun _ => -1) 0 0 ⟨3, [⟨-7, 1⟩, ⟨1, 1⟩]⟩ 4 = some (none, some ⟨4, [-15, 1]⟩))) then throw (IO.userError "negative-profile")
  if !(decide (resumedView 1 (fun _ => 0) 0 0 ⟨7, [⟨0, 1⟩, ⟨1, 1⟩]⟩ 2 = some (none, some ⟨7, [0, 1]⟩))) then throw (IO.userError "smaller-window")
  if !(decide (resumedView 0 (fun _ => 0) 0 (-1) ⟨0, [⟨1, 1⟩]⟩ 3 = some (none, some ⟨3, [1]⟩))) then throw (IO.userError "absorbed-failure")
  if !(decide ((restoreFromExternal? 0 (fun _ => 0) 0 0 ⟨0, [⟨1, 1⟩]⟩).isNone = true)) then throw (IO.userError "absorbed-success-rejected")
  IO.println "QUOTA_CANONICAL_WIRE_OK 29"

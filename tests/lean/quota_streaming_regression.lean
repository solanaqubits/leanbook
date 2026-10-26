/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaTabularContract

-- empty quota
example : chooseQuotaBudgetStreamingWithin 0 (fun _ => 2) 0 (0) 0 = some 0 := by decide +kernel
-- absorbed boundary
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => -1) 2 (0) 3 = some 0 := by decide +kernel
-- absorbed outside
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 2) 7 (0) 0 = some 0 := by decide +kernel
-- absorbed negative
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 2) 3 (-1) 3 = none := by decide +kernel
-- empty negative
example : chooseQuotaBudgetStreamingWithin 0 (fun _ => 0) 0 (-1) 0 = none := by decide +kernel
-- cap zero fails
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 0 = none := by decide +kernel
-- cap zero succeeds
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (1) 0 = some 0 := by decide +kernel
-- insufficient window
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 3 = none := by decide +kernel
-- minimum four
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 4 = some 4 := by decide +kernel
-- first not last
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 6 = some 4 := by decide +kernel
-- minimum six
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (1/8) 6 = some 6 := by decide +kernel
-- exact deficit
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (5/16) 4 = some 4 := by decide +kernel
-- previous exact rejection
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (5/16) 3 = none := by decide +kernel
-- nonmonotone first
example : chooseQuotaBudgetStreamingWithin 1 (fun _ => 2) 0 (-1) 2 = some 1 := by decide +kernel
-- nonmonotone later
example : chooseQuotaBudgetStreamingWithin 1 (fun _ => 2) 0 (0) 4 = some 1 := by decide +kernel
-- negative profile
example : chooseQuotaBudgetStreamingWithin 1 (fun _ => -1) 0 (0) 4 = none := by decide +kernel
-- zero profile
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 0) 0 (0) 4 = none := by decide +kernel
-- unit profile
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1) 0 (0) 2 = some 2 := by decide +kernel
-- unit insufficient
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1) 0 (0) 1 = none := by decide +kernel
-- heterogeneous
example : chooseQuotaBudgetStreamingWithin 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/4) 3 = some 3
  := by decide +kernel
-- single quota
example : chooseQuotaBudgetStreamingWithin 1 (fun _ => 1/2) 0 (1/8) 3 = some 3 := by decide +kernel
-- positive state
example : chooseQuotaBudgetStreamingWithin 3 (fun _ => 1) 1 (0) 2 = some 2 := by decide +kernel
-- large tolerance
example : chooseQuotaBudgetStreamingWithin 3 (fun _ => -1) 0 (2) 4 = some 0 := by decide +kernel
-- negative tolerance
example : chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (-1) 4 = none := by decide +kernel

example (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    chooseQuotaBudgetStreamingWithin n p j ε cap = chooseQuotaBudgetWithin n p j ε cap :=
  chooseQuotaBudgetStreamingWithin_eq n p j ε cap

-- Resume from a valid nonzero row; fuel zero still checks that row.
example : quotaStreamingScan 2 (fun _ => 1/2) 0 (2/5) 0 4 (quotaRow 2 (fun _ => 1/2) 4) = some 4
  := by decide +kernel
example : quotaStreamingScan 2 (fun _ => 1/2) 0 (2/5) 1 3 (quotaRow 2 (fun _ => 1/2) 3) = some 4
  := by decide +kernel

def main : IO Unit := do
  unless chooseQuotaBudgetStreamingWithin 0 (fun _ => 2) 0 (0) 0 == (some 0) &&
    chooseQuotaBudgetStreamingWithin 0 (fun _ => 2) 0 (0) 0 == chooseQuotaBudgetWithin 0 (fun _ =>
    2) 0 (0) 0 do
    throw (IO.userError "empty quota")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => -1) 2 (0) 3 == (some 0) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => -1) 2 (0) 3 == chooseQuotaBudgetWithin 2 (fun _ =>
    -1) 2 (0) 3 do
    throw (IO.userError "absorbed boundary")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 2) 7 (0) 0 == (some 0) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 2) 7 (0) 0 == chooseQuotaBudgetWithin 2 (fun _ =>
    2) 7 (0) 0 do
    throw (IO.userError "absorbed outside")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 2) 3 (-1) 3 == (none) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 2) 3 (-1) 3 == chooseQuotaBudgetWithin 2 (fun _ =>
    2) 3 (-1) 3 do
    throw (IO.userError "absorbed negative")
  unless chooseQuotaBudgetStreamingWithin 0 (fun _ => 0) 0 (-1) 0 == (none) &&
    chooseQuotaBudgetStreamingWithin 0 (fun _ => 0) 0 (-1) 0 == chooseQuotaBudgetWithin 0 (fun _ =>
    0) 0 (-1) 0 do
    throw (IO.userError "empty negative")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 0 == (none) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 0 == chooseQuotaBudgetWithin 2 (fun _
    => 1/2) 0 (2/5) 0 do
    throw (IO.userError "cap zero fails")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (1) 0 == (some 0) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (1) 0 == chooseQuotaBudgetWithin 2 (fun _
    => 1/2) 0 (1) 0 do
    throw (IO.userError "cap zero succeeds")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 3 == (none) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 3 == chooseQuotaBudgetWithin 2 (fun _
    => 1/2) 0 (2/5) 3 do
    throw (IO.userError "insufficient window")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 4 == (some 4) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 4 == chooseQuotaBudgetWithin 2 (fun _
    => 1/2) 0 (2/5) 4 do
    throw (IO.userError "minimum four")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 6 == (some 4) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (2/5) 6 == chooseQuotaBudgetWithin 2 (fun _
    => 1/2) 0 (2/5) 6 do
    throw (IO.userError "first not last")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (1/8) 6 == (some 6) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (1/8) 6 == chooseQuotaBudgetWithin 2 (fun _
    => 1/2) 0 (1/8) 6 do
    throw (IO.userError "minimum six")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (5/16) 4 == (some 4) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (5/16) 4 == chooseQuotaBudgetWithin 2 (fun
    _ => 1/2) 0 (5/16) 4 do
    throw (IO.userError "exact deficit")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (5/16) 3 == (none) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (5/16) 3 == chooseQuotaBudgetWithin 2 (fun
    _ => 1/2) 0 (5/16) 3 do
    throw (IO.userError "previous exact rejection")
  unless chooseQuotaBudgetStreamingWithin 1 (fun _ => 2) 0 (-1) 2 == (some 1) &&
    chooseQuotaBudgetStreamingWithin 1 (fun _ => 2) 0 (-1) 2 == chooseQuotaBudgetWithin 1 (fun _ =>
    2) 0 (-1) 2 do
    throw (IO.userError "nonmonotone first")
  unless chooseQuotaBudgetStreamingWithin 1 (fun _ => 2) 0 (0) 4 == (some 1) &&
    chooseQuotaBudgetStreamingWithin 1 (fun _ => 2) 0 (0) 4 == chooseQuotaBudgetWithin 1 (fun _ =>
    2) 0 (0) 4 do
    throw (IO.userError "nonmonotone later")
  unless chooseQuotaBudgetStreamingWithin 1 (fun _ => -1) 0 (0) 4 == (none) &&
    chooseQuotaBudgetStreamingWithin 1 (fun _ => -1) 0 (0) 4 == chooseQuotaBudgetWithin 1 (fun _ =>
    -1) 0 (0) 4 do
    throw (IO.userError "negative profile")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 0) 0 (0) 4 == (none) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 0) 0 (0) 4 == chooseQuotaBudgetWithin 2 (fun _ =>
    0) 0 (0) 4 do
    throw (IO.userError "zero profile")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1) 0 (0) 2 == (some 2) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1) 0 (0) 2 == chooseQuotaBudgetWithin 2 (fun _ =>
    1) 0 (0) 2 do
    throw (IO.userError "unit profile")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1) 0 (0) 1 == (none) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1) 0 (0) 1 == chooseQuotaBudgetWithin 2 (fun _ =>
    1) 0 (0) 1 do
    throw (IO.userError "unit insufficient")
  unless chooseQuotaBudgetStreamingWithin 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/4) 3 == (some
    3) && chooseQuotaBudgetStreamingWithin 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/4) 3 ==
    chooseQuotaBudgetWithin 2 (fun i => if i = 0 then 1 else 1/2) 0 (1/4) 3 do
    throw (IO.userError "heterogeneous")
  unless chooseQuotaBudgetStreamingWithin 1 (fun _ => 1/2) 0 (1/8) 3 == (some 3) &&
    chooseQuotaBudgetStreamingWithin 1 (fun _ => 1/2) 0 (1/8) 3 == chooseQuotaBudgetWithin 1 (fun _
    => 1/2) 0 (1/8) 3 do
    throw (IO.userError "single quota")
  unless chooseQuotaBudgetStreamingWithin 3 (fun _ => 1) 1 (0) 2 == (some 2) &&
    chooseQuotaBudgetStreamingWithin 3 (fun _ => 1) 1 (0) 2 == chooseQuotaBudgetWithin 3 (fun _ =>
    1) 1 (0) 2 do
    throw (IO.userError "positive state")
  unless chooseQuotaBudgetStreamingWithin 3 (fun _ => -1) 0 (2) 4 == (some 0) &&
    chooseQuotaBudgetStreamingWithin 3 (fun _ => -1) 0 (2) 4 == chooseQuotaBudgetWithin 3 (fun _ =>
    -1) 0 (2) 4 do
    throw (IO.userError "large tolerance")
  unless chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (-1) 4 == (none) &&
    chooseQuotaBudgetStreamingWithin 2 (fun _ => 1/2) 0 (-1) 4 == chooseQuotaBudgetWithin 2 (fun _
    => 1/2) 0 (-1) 4 do
    throw (IO.userError "negative tolerance")
  IO.println "QUOTA_STREAMING_OK 24"

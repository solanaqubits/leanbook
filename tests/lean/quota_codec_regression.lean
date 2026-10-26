import Verification.CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaSnapshotContract
set_option maxRecDepth 8192

-- valid_0
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case0 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 0]⟩ = some ⟨0, []⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case0 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨0, []⟩ = ⟨#[81, 67, 83, 1, 0, 0]⟩ := by decide +kernel
-- valid_1
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case1 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ =
  some ⟨0, [(0 / 1 : ℚ)]⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case1 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨0, [(0 / 1 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ := by decide +kernel
-- valid_2
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case2 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 127, 2, 0, 1, 2, 1, 2,
  3]⟩ = some ⟨127, [(1 / 2 : ℚ), (-2 / 3 : ℚ)]⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case2 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨127, [(1 / 2 : ℚ), (-2 / 3 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 127, 2, 0, 1, 2, 1, 2,
  3]⟩ := by decide +kernel
-- valid_3
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case3 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 1, 1, 0, 128, 1,
  129, 1]⟩ = some ⟨128, [(128 / 129 : ℚ)]⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case3 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨128, [(128 / 129 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 128, 1, 1, 0, 128, 1, 129, 1]⟩
  := by decide +kernel
-- valid_4
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case4 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 255, 127, 1, 1, 129,
  1, 128, 1]⟩ = some ⟨16383, [(-129 / 128 : ℚ)]⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case4 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨16383, [(-129 / 128 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 255, 127, 1, 1, 129, 1, 128, 1]⟩
  := by decide +kernel
-- valid_5
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case5 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 128, 1, 1, 0,
  128, 128, 1, 129, 128, 1]⟩ = some ⟨16384, [(16384 / 16385 : ℚ)]⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case5 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨16384, [(16384 / 16385 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 128, 128, 1, 1, 0, 128, 128,
  1, 129, 128, 1]⟩ := by decide +kernel
-- valid_6
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case6 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 1, 1, 0, 129, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 128, 8, 131, 128, 128, 128, 128, 128, 128, 128, 128, 128,
  1]⟩ = some ⟨1, [(1208925819614629174706177 / 1180591620717411303427 : ℚ)]⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case6 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨1, [(1208925819614629174706177 / 1180591620717411303427 : ℚ)]⟩ = ⟨#[81, 67, 83,
  1, 1, 1, 0, 129, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 8, 131, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 1]⟩ := by decide +kernel
-- zero_bound_and_row_limits
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case7 : Bool := decide (strictDecode ⟨6, 0, 0⟩ ⟨#[81, 67, 83, 1, 0, 0]⟩ = some ⟨0, []⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case7 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨0, []⟩ = ⟨#[81, 67, 83, 1, 0, 0]⟩ := by decide +kernel
-- exact_byte_limit
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case8 : Bool := decide (strictDecode ⟨9, 0, 1⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ = some ⟨0, [(0
  / 1 : ℚ)]⟩)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case8 = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : encodeV1 ⟨0, [(0 / 1 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ := by decide +kernel
-- size_one_short
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case9 : Bool := decide (strictDecode ⟨8, 0, 1⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case9 = true := by decide +kernel
-- size_zero
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case10 : Bool := decide (strictDecode ⟨0, 0, 0⟩ ⟨#[81, 67, 83, 1, 0, 0]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case10 = true := by decide +kernel
-- bound_over
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case11 : Bool := decide (strictDecode ⟨4096, 127, 64⟩ ⟨#[81, 67, 83, 1, 128, 1, 0]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case11 = true := by decide +kernel
-- row_over
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case12 : Bool := decide (strictDecode ⟨4096, 0, 0⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case12 = true := by decide +kernel
-- empty
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case13 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case13 = true := by decide +kernel
-- truncated_0
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case14 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case14 = true := by decide +kernel
-- truncated_1
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case15 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case15 = true := by decide +kernel
-- truncated_2
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case16 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case16 = true := by decide +kernel
-- truncated_3
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case17 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case17 = true := by decide +kernel
-- truncated_4
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case18 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case18 = true := by decide +kernel
-- truncated_5
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case19 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case19 = true := by decide +kernel
-- truncated_6
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case20 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case20 = true := by decide +kernel
-- truncated_7
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case21 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case21 = true := by decide +kernel
-- truncated_8
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case22 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case22 = true := by decide +kernel
-- bad_magic
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case23 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[80, 67, 83, 1, 0, 1, 0, 1, 2]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case23 = true := by decide +kernel
-- bad_version
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case24 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 2, 0, 1, 0, 1, 2]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case24 = true := by decide +kernel
-- trailing
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case25 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 2, 0]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case25 = true := by decide +kernel
-- count_too_small
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case26 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 0, 0, 1, 2]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case26 = true := by decide +kernel
-- count_too_large
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case27 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 2, 0, 1, 2]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case27 = true := by decide +kernel
-- sign2
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case28 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 2, 1, 2]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case28 = true := by decide +kernel
-- sign255
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case29 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 255, 1, 2]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case29 = true := by decide +kernel
-- den0
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case30 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 0]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case30 = true := by decide +kernel
-- unreduced
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case31 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 2, 4]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case31 = true := by decide +kernel
-- negative_zero
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case32 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 1, 0, 1]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case32 = true := by decide +kernel
-- zero_over5
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case33 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 5]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case33 = true := by decide +kernel
-- padded_num
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case34 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 129, 0, 2]⟩
  = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case34 = true := by decide +kernel
-- padded_den
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case35 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 130, 0]⟩
  = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case35 = true := by decide +kernel
-- truncated_num
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case36 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 128]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case36 = true := by decide +kernel
-- truncated_den
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case37 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 128]⟩ =
  none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case37 = true := by decide +kernel
-- padded_bound
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case38 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 0, 0]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case38 = true := by decide +kernel
-- padded_count
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case39 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 128, 0]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case39 = true := by decide +kernel
-- huge_count
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case40 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 128, 8]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case40 = true := by decide +kernel
-- huge_bound
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def case41 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 128, 128, 128,
  128, 128, 128, 128, 128, 128, 128, 8, 0]⟩ = none)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : case41 = true := by decide +kernel

-- Format-valid empty row does not become a mathematical cursor.
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : restoreCursor? 0 (fun _ => 0) 0 0 ⟨0, []⟩ = none := by decide +kernel

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  unless case0 do throw (IO.userError "valid_0")
  unless case1 do throw (IO.userError "valid_1")
  unless case2 do throw (IO.userError "valid_2")
  unless case3 do throw (IO.userError "valid_3")
  unless case4 do throw (IO.userError "valid_4")
  unless case5 do throw (IO.userError "valid_5")
  unless case6 do throw (IO.userError "valid_6")
  unless case7 do throw (IO.userError "zero_bound_and_row_limits")
  unless case8 do throw (IO.userError "exact_byte_limit")
  unless case9 do throw (IO.userError "size_one_short")
  unless case10 do throw (IO.userError "size_zero")
  unless case11 do throw (IO.userError "bound_over")
  unless case12 do throw (IO.userError "row_over")
  unless case13 do throw (IO.userError "empty")
  unless case14 do throw (IO.userError "truncated_0")
  unless case15 do throw (IO.userError "truncated_1")
  unless case16 do throw (IO.userError "truncated_2")
  unless case17 do throw (IO.userError "truncated_3")
  unless case18 do throw (IO.userError "truncated_4")
  unless case19 do throw (IO.userError "truncated_5")
  unless case20 do throw (IO.userError "truncated_6")
  unless case21 do throw (IO.userError "truncated_7")
  unless case22 do throw (IO.userError "truncated_8")
  unless case23 do throw (IO.userError "bad_magic")
  unless case24 do throw (IO.userError "bad_version")
  unless case25 do throw (IO.userError "trailing")
  unless case26 do throw (IO.userError "count_too_small")
  unless case27 do throw (IO.userError "count_too_large")
  unless case28 do throw (IO.userError "sign2")
  unless case29 do throw (IO.userError "sign255")
  unless case30 do throw (IO.userError "den0")
  unless case31 do throw (IO.userError "unreduced")
  unless case32 do throw (IO.userError "negative_zero")
  unless case33 do throw (IO.userError "zero_over5")
  unless case34 do throw (IO.userError "padded_num")
  unless case35 do throw (IO.userError "padded_den")
  unless case36 do throw (IO.userError "truncated_num")
  unless case37 do throw (IO.userError "truncated_den")
  unless case38 do throw (IO.userError "padded_bound")
  unless case39 do throw (IO.userError "padded_count")
  unless case40 do throw (IO.userError "huge_count")
  unless case41 do throw (IO.userError "huge_bound")
  IO.println "QUOTA_CODEC_OK 42"

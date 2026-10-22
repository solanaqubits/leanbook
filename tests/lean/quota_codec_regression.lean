import Verification.CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaSnapshotContract
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

-- valid_0
def case0 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 0]⟩ = some ⟨0, []⟩)
example : case0 = true := by decide +kernel
example : encodeV1 ⟨0, []⟩ = ⟨#[81, 67, 83, 1, 0, 0]⟩ := by decide +kernel
-- valid_1
def case1 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ = some ⟨0, [(0 / 1 : ℚ)]⟩)
example : case1 = true := by decide +kernel
example : encodeV1 ⟨0, [(0 / 1 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ := by decide +kernel
-- valid_2
def case2 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 127, 2, 0, 1, 2, 1, 2, 3]⟩ = some ⟨127, [(1 / 2 : ℚ), (-2 / 3 : ℚ)]⟩)
example : case2 = true := by decide +kernel
example : encodeV1 ⟨127, [(1 / 2 : ℚ), (-2 / 3 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 127, 2, 0, 1, 2, 1, 2, 3]⟩ := by decide +kernel
-- valid_3
def case3 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 1, 1, 0, 128, 1, 129, 1]⟩ = some ⟨128, [(128 / 129 : ℚ)]⟩)
example : case3 = true := by decide +kernel
example : encodeV1 ⟨128, [(128 / 129 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 128, 1, 1, 0, 128, 1, 129, 1]⟩ := by decide +kernel
-- valid_4
def case4 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 255, 127, 1, 1, 129, 1, 128, 1]⟩ = some ⟨16383, [(-129 / 128 : ℚ)]⟩)
example : case4 = true := by decide +kernel
example : encodeV1 ⟨16383, [(-129 / 128 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 255, 127, 1, 1, 129, 1, 128, 1]⟩ := by decide +kernel
-- valid_5
def case5 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 128, 1, 1, 0, 128, 128, 1, 129, 128, 1]⟩ = some ⟨16384, [(16384 / 16385 : ℚ)]⟩)
example : case5 = true := by decide +kernel
example : encodeV1 ⟨16384, [(16384 / 16385 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 128, 128, 1, 1, 0, 128, 128, 1, 129, 128, 1]⟩ := by decide +kernel
-- valid_6
def case6 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 1, 1, 0, 129, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 8, 131, 128, 128, 128, 128, 128, 128, 128, 128, 128, 1]⟩ = some ⟨1, [(1208925819614629174706177 / 1180591620717411303427 : ℚ)]⟩)
example : case6 = true := by decide +kernel
example : encodeV1 ⟨1, [(1208925819614629174706177 / 1180591620717411303427 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 1, 1, 0, 129, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 8, 131, 128, 128, 128, 128, 128, 128, 128, 128, 128, 1]⟩ := by decide +kernel
-- zero_bound_and_row_limits
def case7 : Bool := decide (strictDecode ⟨6, 0, 0⟩ ⟨#[81, 67, 83, 1, 0, 0]⟩ = some ⟨0, []⟩)
example : case7 = true := by decide +kernel
example : encodeV1 ⟨0, []⟩ = ⟨#[81, 67, 83, 1, 0, 0]⟩ := by decide +kernel
-- exact_byte_limit
def case8 : Bool := decide (strictDecode ⟨9, 0, 1⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ = some ⟨0, [(0 / 1 : ℚ)]⟩)
example : case8 = true := by decide +kernel
example : encodeV1 ⟨0, [(0 / 1 : ℚ)]⟩ = ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ := by decide +kernel
-- size_one_short
def case9 : Bool := decide (strictDecode ⟨8, 0, 1⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ = none)
example : case9 = true := by decide +kernel
-- size_zero
def case10 : Bool := decide (strictDecode ⟨0, 0, 0⟩ ⟨#[81, 67, 83, 1, 0, 0]⟩ = none)
example : case10 = true := by decide +kernel
-- bound_over
def case11 : Bool := decide (strictDecode ⟨4096, 127, 64⟩ ⟨#[81, 67, 83, 1, 128, 1, 0]⟩ = none)
example : case11 = true := by decide +kernel
-- row_over
def case12 : Bool := decide (strictDecode ⟨4096, 0, 0⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 1]⟩ = none)
example : case12 = true := by decide +kernel
-- empty
def case13 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[]⟩ = none)
example : case13 = true := by decide +kernel
-- truncated_0
def case14 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[]⟩ = none)
example : case14 = true := by decide +kernel
-- truncated_1
def case15 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81]⟩ = none)
example : case15 = true := by decide +kernel
-- truncated_2
def case16 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67]⟩ = none)
example : case16 = true := by decide +kernel
-- truncated_3
def case17 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83]⟩ = none)
example : case17 = true := by decide +kernel
-- truncated_4
def case18 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1]⟩ = none)
example : case18 = true := by decide +kernel
-- truncated_5
def case19 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0]⟩ = none)
example : case19 = true := by decide +kernel
-- truncated_6
def case20 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1]⟩ = none)
example : case20 = true := by decide +kernel
-- truncated_7
def case21 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0]⟩ = none)
example : case21 = true := by decide +kernel
-- truncated_8
def case22 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1]⟩ = none)
example : case22 = true := by decide +kernel
-- bad_magic
def case23 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[80, 67, 83, 1, 0, 1, 0, 1, 2]⟩ = none)
example : case23 = true := by decide +kernel
-- bad_version
def case24 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 2, 0, 1, 0, 1, 2]⟩ = none)
example : case24 = true := by decide +kernel
-- trailing
def case25 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 2, 0]⟩ = none)
example : case25 = true := by decide +kernel
-- count_too_small
def case26 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 0, 0, 1, 2]⟩ = none)
example : case26 = true := by decide +kernel
-- count_too_large
def case27 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 2, 0, 1, 2]⟩ = none)
example : case27 = true := by decide +kernel
-- sign2
def case28 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 2, 1, 2]⟩ = none)
example : case28 = true := by decide +kernel
-- sign255
def case29 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 255, 1, 2]⟩ = none)
example : case29 = true := by decide +kernel
-- den0
def case30 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 0]⟩ = none)
example : case30 = true := by decide +kernel
-- unreduced
def case31 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 2, 4]⟩ = none)
example : case31 = true := by decide +kernel
-- negative_zero
def case32 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 1, 0, 1]⟩ = none)
example : case32 = true := by decide +kernel
-- zero_over5
def case33 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 0, 5]⟩ = none)
example : case33 = true := by decide +kernel
-- padded_num
def case34 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 129, 0, 2]⟩ = none)
example : case34 = true := by decide +kernel
-- padded_den
def case35 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 130, 0]⟩ = none)
example : case35 = true := by decide +kernel
-- truncated_num
def case36 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 128]⟩ = none)
example : case36 = true := by decide +kernel
-- truncated_den
def case37 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 1, 0, 1, 128]⟩ = none)
example : case37 = true := by decide +kernel
-- padded_bound
def case38 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 0, 0]⟩ = none)
example : case38 = true := by decide +kernel
-- padded_count
def case39 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 128, 0]⟩ = none)
example : case39 = true := by decide +kernel
-- huge_count
def case40 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 0, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 8]⟩ = none)
example : case40 = true := by decide +kernel
-- huge_bound
def case41 : Bool := decide (strictDecode ⟨4096, 100000, 64⟩ ⟨#[81, 67, 83, 1, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 8, 0]⟩ = none)
example : case41 = true := by decide +kernel

-- Format-valid empty row does not become a mathematical cursor.
example : restoreCursor? 0 (fun _ => 0) 0 0 ⟨0, []⟩ = none := by decide +kernel

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

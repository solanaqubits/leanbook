import Verification.MlDsaProductionConversionBlock

open MlDsaRt1 MlDsaU128Conversion MlDsaProductionConversionBlock

private def narrowCells (r : Nat) : BlockCells := ⟨r, 1, 0, 0, 0, 0, 0⟩
private def wideCells (x y : Nat) : BlockCells :=
  let shifted := (x * u128Bound) % cairoPrime
  let difference := (x + (cairoPrime - maxHigh)) % cairoPrime
  let checked := if difference = 0 then (y + (u128Bound - 1)) % cairoPrime
    else (x + (u128Bound - maxHigh)) % cairoPrime
  ⟨(shifted + y) % cairoPrime, 0, shifted, difference, checked, x, y⟩

example : blockWords.length = 23 := block_sizes.1
example : instructionOffsets.length = 14 := block_sizes.2
example : decodeFields (blockWords[0]! + 1) ≠ decodeFields (blockWords[0]!) := by decide
example : 1292 + blockWords[19]! = 1309 := by decide
example : 1292 + (blockWords[19]! + 1) ≠ 1309 := by decide

example : ExitAssertions (narrowCells 0) (.narrow 0) := by
  unfold ExitAssertions narrowCells
  decide
example : ExitAssertions (narrowCells (u128Bound - 1)) (.narrow (u128Bound - 1)) := by
  unfold ExitAssertions narrowCells
  decide
example : ¬ ExitAssertions (narrowCells u128Bound) (.narrow u128Bound) := by
  unfold ExitAssertions narrowCells
  decide
example : ¬ ExitAssertions (narrowCells 1) (.narrow 2) := by
  unfold ExitAssertions narrowCells
  decide
example : ¬ ExitAssertions { narrowCells 0 with selector := 0 } (.narrow 0) := by
  unfold ExitAssertions narrowCells
  decide
example : WideAssertions (wideCells 1 0) := by
  unfold WideAssertions wideCells
  decide
example : WideAssertions (wideCells maxHigh 0) := by
  unfold WideAssertions wideCells
  decide
example : ¬ WideAssertions (wideCells maxHigh 1) := by
  unfold WideAssertions wideCells
  decide
example : ¬ WideAssertions (wideCells 0 1) := by
  unfold WideAssertions wideCells
  decide
example : ExitAssertions (wideCells 1 0) (.wide 1 0) := by
  unfold ExitAssertions WideAssertions wideCells
  decide
example : ¬ ExitAssertions (wideCells 1 0) (.wide 2 0) := by
  unfold ExitAssertions WideAssertions wideCells
  decide
example (v : Nat) (hv : v < cairoPrime) : v ≠ (v + 1) % cairoPrime :=
  failure_assert_impossible hv
example (s : BlockCells) (hr : s.input < u128Bound) : ¬ WideAssertions s :=
  no_wide_assertions_of_lt hr
example (s : BlockCells) (out : ConversionResult) (h : ExitAssertions s out) :
    ConversionChecks s.input out := exitAssertions_to_checks h
example (w : Nat) (hw : w < 2 ^ 128) (s : BlockCells)
    (hin : s.input = rt1FieldExpr w rt1Mask) (out : ConversionResult)
    (h : ExitAssertions s out) : out = .narrow (packRotl64_1 w) :=
  rt1_exit_is_narrow hw hin h

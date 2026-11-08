import Verification.MlDsaU128Conversion

/-! Numeric branch boundaries and counterexamples to weakened constraints.
These checks supplement universal proofs; they are not executions of Cairo. -/
open MlDsaRt1 MlDsaU128Conversion

example : ConversionChecks 0 (.narrow 0) := by
  unfold ConversionChecks
  decide
example : ConversionChecks (u128Bound - 1) (.narrow (u128Bound - 1)) := by
  unfold ConversionChecks
  decide
example : ¬ ConversionChecks u128Bound (.narrow u128Bound) := by
  unfold ConversionChecks
  decide
example : ¬ ConversionChecks 1 (.narrow 2) := by
  unfold ConversionChecks
  decide
example : WideChecks u128Bound 1 0 := by
  unfold WideChecks WideRangeCheck
  decide
example : WideChecks (u128Bound + 1) 1 1 := by
  unfold WideChecks WideRangeCheck
  decide
example : WideChecks (cairoPrime - 1) maxHigh 0 := by
  unfold WideChecks WideRangeCheck
  decide
example : ¬ WideChecks 0 maxHigh 1 := by
  unfold WideChecks WideRangeCheck
  decide
example : ¬ WideChecks 1 0 1 := by
  unfold WideChecks WideRangeCheck
  decide
example : ¬ WideChecks (u128Bound - 1) (maxHigh + 1) 0 := by
  unfold WideChecks WideRangeCheck
  decide
example : WideRangeCheck maxHigh 0 := by
  unfold WideRangeCheck
  decide
example : ¬ WideRangeCheck maxHigh 1 := by
  unfold WideRangeCheck
  decide
example : WideRangeCheck (maxHigh - 1) (u128Bound - 1) := by
  unfold WideRangeCheck
  decide
example : ¬ WideRangeCheck (maxHigh + 1) 0 := by
  unfold WideRangeCheck
  decide

-- Without the adjusted check, nonzero high can recompose to zero modulo P.
example : maxHigh < u128Bound ∧ 1 < u128Bound ∧ maxHigh ≠ 0 ∧
    (maxHigh * u128Bound + 1) % cairoPrime = 0 := by
  decide
-- The other cap branch is also necessary: high=maxHigh+1 wraps below U.
example : (maxHigh + 1) < u128Bound ∧
    ((maxHigh + 1) * u128Bound) % cairoPrime = u128Bound - 1 := by
  decide
-- The nonzero-high check is necessary to exclude a low input from Wide.
example : WideRangeCheck 0 1 ∧ (0 * u128Bound + 1) % cairoPrime = 1 := by
  unfold WideRangeCheck
  decide

example (r x y : Nat) (hr : r < u128Bound) : ¬ WideChecks r x y :=
  not_wideChecks_of_lt hr
example (r : Nat) (hr : r < u128Bound) (out : ConversionResult) :
    ConversionChecks r out ↔ out = .narrow r := conversionChecks_lt_iff hr out
example (w : Nat) (hw : w < 2 ^ 128) (out : ConversionResult) :
    ConversionChecks (rt1FieldExpr w rt1Mask) out ↔
      out = .narrow (packRotl64_1 w) := rt1_conversionChecks_iff hw out
example (w x y : Nat) (hw : w < 2 ^ 128) :
    ¬ WideChecks (rt1FieldExpr w rt1Mask) x y := rt1_not_wide hw
example (w : Nat) (hw : w < 2 ^ 128) (out : ConversionResult)
    (h : ConversionChecks (rt1FieldExpr w rt1Mask) out) :
    resultOption out = some (packRotl64_1 w) := rt1_resultOption_eq_some hw h
example : ConversionChecks (rt1FieldExpr (2 ^ 63) rt1Mask) (.narrow 1) := by
  unfold ConversionChecks
  decide
example : ConversionChecks (rt1FieldExpr (2 ^ 127) rt1Mask) (.narrow (2 ^ 64)) := by
  unfold ConversionChecks
  decide
example : resultOption (.wide 1 0) = none := by rfl

example (x : Nat) (hx : x < u128Bound) :
    (x + cairoPrime - maxHigh) % cairoPrime = 0 ↔ x = maxHigh := high_is_max_iff hx
example : ¬ ConversionChecks cairoPrime (.narrow 0) := by
  unfold ConversionChecks
  decide

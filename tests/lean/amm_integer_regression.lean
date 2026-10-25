import Verification.DeFiAMMIntegerSwap
open DeFiAMMIntegerSwap
example : DeFiAMMIntegerSwapSuite := verification_suite
example : output 100 100 1000 997 10 = 9 := by decide
example : output 100 100 1000 997 1 = 0 := by decide
example : output 100 100 1000 997 0 = 0 := zero_input _ _ _ _
example : 100 * 100 ≤ (100 + 10) * (100 - output 100 100 1000 997 10) :=
  reserve_product_nondecreasing (by decide) (by decide) (by decide) (by decide)
example : output 1 1 1000 997 1000000 = 0 := by decide
example : output 1 100 1000 997 1000000 < 100 :=
  output_lt_reserve (by decide) (by decide) (by decide)
example : output 100 100 1 0 100 = 0 := by decide
-- A multiplier greater than one is excluded for a reason: it can reduce the product.
example : (100 + 10) * (100 - output 100 100 1 2 10) < 100 * 100 := by decide
example : output 100 100 1000 997 10 * denominator 100 1000 997 10 ≤ 100 * (997 * 10) ∧
    100 * (997 * 10) < (output 100 100 1000 997 10 + 1) * denominator 100 1000 997 10 :=
  rounding_bounds (by decide) (by decide)

import Verification.DeFiAMMExactOutput
open DeFiAMMInvariants DeFiAMMExactOutput
example : DeFiAMMExactOutputSuite := verification_suite
example : requiredInput 100 100 1 10 = 100 / 9 := by norm_num [requiredInput]
example : swapOutputY 100 100 1 (requiredInput 100 100 1 10) = 10 :=
  output_of_required (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : swapOutputY 100 100 1 10 < 10 := by norm_num [swapOutputY]
example : 10 ≤ swapOutputY 100 100 1 12 := by norm_num [swapOutputY]
example : requiredInput 100 100 (99 / 100) 10 = 10000 / 891 := by norm_num [requiredInput]
example (dx : ℝ) (hd : 0 < dx) :
    10 ≤ swapOutputY 100 100 1 dx ↔ requiredInput 100 100 1 10 ≤ dx :=
  minimum_input_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd
-- Outside the domain, field division by zero is not a feasible swap quotation.
example : requiredInput 100 100 1 100 = 0 := by norm_num [requiredInput]
example : swapOutputY 100 100 1 (requiredInput 100 100 1 100) ≠ 100 := by
  norm_num [requiredInput, swapOutputY]

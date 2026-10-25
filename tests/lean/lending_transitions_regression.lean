import Verification.DeFiLendingUtilizationTransitions
open DeFiLendingUtilizationTransitions
 def s : State := ⟨100, 50, 10, by norm_num, by norm_num, by norm_num, by norm_num⟩
example : DeFiLendingUtilizationTransitionsSuite := verification_suite
example : assets s = 140 := by norm_num [assets, s]
example : usage s = 5 / 14 := by norm_num [usage, assets, s]
example : usage (borrow s 70 (by norm_num) (by norm_num [s])) = 6 / 7 := by
  norm_num [usage, assets, borrow, s]
example : usage (repay s 20 (by norm_num) (by norm_num [s])) = 3 / 14 := by
  norm_num [usage, assets, repay, s]
example : usage (repay s s.debt s.debt_nonneg le_rfl) = 0 := full_repayment_zero s
example : ¬ (100 : ℚ) ≤ s.cash - s.reserves := by norm_num [s]
example : ¬ (60 : ℚ) ≤ s.debt := by norm_num [s]
example (d : ℚ) (h0 : 0 ≤ d) (hc : d ≤ s.cash - s.reserves) :
    assets (borrow s d h0 hc) = 140 := by rw [borrow_assets]; norm_num [assets, s]

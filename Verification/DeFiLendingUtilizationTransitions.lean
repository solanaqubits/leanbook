/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiKinkedInterestRateUtilization

/-! Borrow and repay transitions with reserve coverage and conserved net assets.
This accounting model excludes accrual, defaults, collateral and price changes. -/
namespace DeFiLendingUtilizationTransitions
open DeFiKinkedInterestRateUtilization

structure State where
  cash : ℚ
  debt : ℚ
  reserves : ℚ
  cash_cover : reserves ≤ cash
  debt_nonneg : 0 ≤ debt
  reserves_nonneg : 0 ≤ reserves
  assets_pos : 0 < cash + debt - reserves

def assets (s : State) : ℚ := s.cash + s.debt - s.reserves

def usage (s : State) : ℚ := s.debt / assets s

def borrow (s : State) (d : ℚ) (h0 : 0 ≤ d) (hc : d ≤ s.cash - s.reserves) : State :=
  ⟨s.cash - d, s.debt + d, s.reserves, by linarith,
    add_nonneg s.debt_nonneg h0, s.reserves_nonneg, by linarith [s.assets_pos]⟩

def repay (s : State) (d : ℚ) (h0 : 0 ≤ d) (hd : d ≤ s.debt) : State :=
  ⟨s.cash + d, s.debt - d, s.reserves, by linarith [s.cash_cover],
    sub_nonneg.mpr hd, s.reserves_nonneg, by linarith [s.assets_pos]⟩

theorem usage_eq_existing (s : State) : usage s = utilization s.cash s.debt s.reserves := by
  unfold usage utilization assets denominator
  split_ifs with h
  · simp [h]
  · rfl

theorem usage_bounds (s : State) : 0 ≤ usage s ∧ usage s ≤ 1 := by
  refine ⟨div_nonneg s.debt_nonneg s.assets_pos.le, (div_le_one s.assets_pos).mpr ?_⟩
  linarith [s.cash_cover]

theorem borrow_assets (s : State) (d : ℚ) (h0 : 0 ≤ d) (hc : d ≤ s.cash - s.reserves) :
    assets (borrow s d h0 hc) = assets s := by simp [assets, borrow]

theorem repay_assets (s : State) (d : ℚ) (h0 : 0 ≤ d) (hd : d ≤ s.debt) :
    assets (repay s d h0 hd) = assets s := by simp [assets, repay]

theorem borrow_usage (s : State) (d : ℚ) (h0 : 0 ≤ d) (hc : d ≤ s.cash - s.reserves) :
    usage (borrow s d h0 hc) = usage s + d / assets s := by
  unfold usage
  rw [borrow_assets]
  exact add_div _ _ _

theorem repay_usage (s : State) (d : ℚ) (h0 : 0 ≤ d) (hd : d ≤ s.debt) :
    usage (repay s d h0 hd) = usage s - d / assets s := by
  unfold usage
  rw [repay_assets]
  exact sub_div _ _ _

theorem borrow_rate_increases (P : KinkRateParams) (s : State) (d : ℚ)
    (h0 : 0 ≤ d) (hc : d ≤ s.cash - s.reserves) :
    borrow_rate P (usage s) ≤ borrow_rate P (usage (borrow s d h0 hc)) := by
  apply borrow_rate_monotone P
  rw [borrow_usage]
  exact le_add_of_nonneg_right (div_nonneg h0 s.assets_pos.le)

theorem repay_rate_decreases (P : KinkRateParams) (s : State) (d : ℚ)
    (h0 : 0 ≤ d) (hd : d ≤ s.debt) :
    borrow_rate P (usage (repay s d h0 hd)) ≤ borrow_rate P (usage s) := by
  apply borrow_rate_monotone P
  rw [repay_usage]
  exact sub_le_self _ (div_nonneg h0 s.assets_pos.le)

theorem full_repayment_zero (s : State) :
    usage (repay s s.debt s.debt_nonneg le_rfl) = 0 := by
  rw [repay_usage]
  exact sub_self _

structure DeFiLendingUtilizationTransitionsSuite : Prop where
  borrow_conservation : ∀ (s : State) (d : ℚ) (h0 : 0 ≤ d)
    (hc : d ≤ s.cash - s.reserves), assets (borrow s d h0 hc) = assets s
  repay_conservation : ∀ (s : State) (d : ℚ) (h0 : 0 ≤ d) (hd : d ≤ s.debt),
    assets (repay s d h0 hd) = assets s
  bounds : ∀ s, 0 ≤ usage s ∧ usage s ≤ 1

theorem verification_suite : DeFiLendingUtilizationTransitionsSuite where
  borrow_conservation := borrow_assets
  repay_conservation := repay_assets
  bounds := usage_bounds
end DeFiLendingUtilizationTransitions

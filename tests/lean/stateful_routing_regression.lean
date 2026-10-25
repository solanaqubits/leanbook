import Verification.DeFiStatefulAMMRouting
open DeFiStatefulAMMRouting DeFiAMMInvariants
noncomputable def pool : Pool := ⟨100, 100, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
noncomputable def amount : Amount := ⟨10, by norm_num⟩
noncomputable def market : ℕ → Pool := fun _ => pool
example : DeFiStatefulAMMRoutingSuite := verification_suite
example : (run market amount [(0, false), (1, false)]).2.val = 25 / 3 := by
  norm_num [run, step, trade, swap, market, pool, amount, newRx, newRy, swapOutputY]
example : (run market amount [(0, false), (0, false)]).2.val = 10000 / 1441 := by
  norm_num [run, step, trade, swap, market, pool, amount, newRx, newRy, swapOutputY]
example : (run market amount [(0, false), (0, true)]).2.val = 10 := by
  norm_num [run, step, trade, swap, DeFiStatefulAMMRouting.flip,
    market, pool, amount, newRx, newRy, swapOutputY]
example : (run market amount [(0, false), (0, true)]).1 2 = market 2 :=
  untouched_pool _ _ _ _ (by simp)
example (r : Route ℕ) (i : ℕ) : product (market i) ≤ product ((run market amount r).1 i) :=
  route_product _ _ _ _
example : (run market amount []).2 = amount := rfl
example : 0 < (run market amount [(0, false), (0, false)]).2.val := route_output_positive _ _ _
example : (run market amount [(0, false), (0, false)]).2.val ≠ 25 / 3 := by
  norm_num [run, step, trade, swap, market, pool, amount, newRx, newRy, swapOutputY]

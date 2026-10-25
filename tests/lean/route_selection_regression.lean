import Verification.DeFiFiniteRouteSelection
open DeFiStatefulAMMRouting DeFiFiniteRouteSelection DeFiAMMInvariants
noncomputable def pool : Pool := ⟨100, 100, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
noncomputable def amount : Amount := ⟨10, by norm_num⟩
noncomputable def market : ℕ → Pool := fun _ => pool
example : DeFiFiniteRouteSelectionSuite := verification_suite
example : select market amount [] = none := (no_selection_iff _ _ _).mpr rfl
example : select market amount [[(0, false)]] = some [(0, false)] := List.argmax_singleton
example : executeAtLeast market amount [(0, false)] 10 = none := by
  norm_num [executeAtLeast, quote, run, step, trade, swap, market, pool, amount, swapOutputY]
example : executeAtLeast market amount [(0, false)] 9 = some (run market amount [(0, false)]) := by
  simp only [executeAtLeast]
  have h : (9 : ℝ) ≤ quote market amount [(0, false)] := by
    norm_num [quote, run, step, trade, swap, market, pool, amount, swapOutputY]
  exact if_pos h
example (rs : List (Route ℕ)) (r : Route ℕ) (h : select market amount rs = some r) : r ∈ rs :=
  selected_member _ _ _ _ h
example (rs : List (Route ℕ)) (r r' : Route ℕ) (h : select market amount rs = some r)
    (hr : r' ∈ rs) : quote market amount r' ≤ quote market amount r :=
  selected_optimal _ _ _ _ h _ hr

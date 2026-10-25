/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiStatefulAMMRouting
import Mathlib.Data.List.MinMax

/-! Selection from a caller-supplied finite route list, quoting every route from
one common snapshot. Optimality is within this list; no exhaustive route search,
gas-cost optimization, token compatibility or concurrent-state guarantee. -/
noncomputable section
open DeFiStatefulAMMRouting
namespace DeFiFiniteRouteSelection
variable {ι : Type} [DecidableEq ι]

def quote (s : ι → Pool) (a : Amount) (r : Route ι) : ℝ := (run s a r).2.val

def select (s : ι → Pool) (a : Amount) (routes : List (Route ι)) : Option (Route ι) :=
  routes.argmax (quote s a)

theorem selected_member (s : ι → Pool) (a : Amount) (rs : List (Route ι)) (r : Route ι)
    (h : select s a rs = some r) : r ∈ rs :=
  List.argmax_mem (show r ∈ rs.argmax (quote s a) from h)

theorem selected_optimal (s : ι → Pool) (a : Amount) (rs : List (Route ι)) (r : Route ι)
    (h : select s a rs = some r) (r' : Route ι) (hr : r' ∈ rs) :
    quote s a r' ≤ quote s a r :=
  List.le_of_mem_argmax hr (show r ∈ rs.argmax (quote s a) from h)

theorem no_selection_iff (s : ι → Pool) (a : Amount) (rs : List (Route ι)) :
    select s a rs = none ↔ rs = [] := List.argmax_eq_none

def executeAtLeast (s : ι → Pool) (a : Amount) (r : Route ι) (minimum : ℝ) :
    Option ((ι → Pool) × Amount) :=
  if minimum ≤ quote s a r then some (run s a r) else none

theorem guarded_execution_iff (s : ι → Pool) (a : Amount) (r : Route ι) (minimum : ℝ)
    (out : (ι → Pool) × Amount) :
    executeAtLeast s a r minimum = some out ↔
      out = run s a r ∧ minimum ≤ out.2.val := by
  unfold executeAtLeast quote
  split_ifs with h <;> simp_all [eq_comm]

theorem guarded_product (s : ι → Pool) (a : Amount) (r : Route ι) (minimum : ℝ)
    (out : (ι → Pool) × Amount) (h : executeAtLeast s a r minimum = some out) (j : ι) :
    product (s j) ≤ product (out.1 j) := by
  obtain ⟨rfl, _⟩ := (guarded_execution_iff s a r minimum out).mp h
  exact route_product s a r j

/-- A failed minimum for the best candidate excludes every candidate in the supplied list. -/
theorem best_below_minimum (s : ι → Pool) (a : Amount) (rs : List (Route ι)) (r : Route ι)
    (h : select s a rs = some r) (minimum : ℝ) (hm : quote s a r < minimum) :
    ∀ r' ∈ rs, executeAtLeast s a r' minimum = none := by
  intro r' hr
  have hl := (selected_optimal s a rs r h r' hr).trans_lt hm
  simp [executeAtLeast, not_le.mpr hl]

structure DeFiFiniteRouteSelectionSuite : Prop where
  optimal : ∀ (ι : Type) [DecidableEq ι] (s : ι → Pool) (a : Amount)
    (rs : List (Route ι)) (r : Route ι), select s a rs = some r →
    ∀ r' ∈ rs, quote s a r' ≤ quote s a r
  execution : ∀ (ι : Type) [DecidableEq ι] (s : ι → Pool) (a : Amount)
    (r : Route ι) (m : ℝ) (out : (ι → Pool) × Amount), executeAtLeast s a r m = some out ↔
    out = run s a r ∧ m ≤ out.2.val

theorem verification_suite : DeFiFiniteRouteSelectionSuite where
  optimal := fun _ _ s a rs r h r' hr => selected_optimal s a rs r h r' hr
  execution := fun _ _ s a r m out => guarded_execution_iff s a r m out
end DeFiFiniteRouteSelection

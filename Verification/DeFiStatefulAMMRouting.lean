/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiAMMInvariants

/-! Reserve-updating numeric routes, including repeated pools and reverse swaps.
Asset-address compatibility is a caller precondition; this is not EVM execution. -/
noncomputable section
open DeFiAMMInvariants
namespace DeFiStatefulAMMRouting

structure Pool where
  x : ℝ
  y : ℝ
  fee : ℝ
  x_pos : 0 < x
  y_pos : 0 < y
  fee_pos : 0 < fee
  fee_le : fee ≤ 1

abbrev Amount := {a : ℝ // 0 < a}

def product (p : Pool) : ℝ := p.x * p.y

def flip (p : Pool) : Pool := ⟨p.y, p.x, p.fee, p.y_pos, p.x_pos, p.fee_pos, p.fee_le⟩

def swap (p : Pool) (a : Amount) : Pool × Amount :=
  (⟨newRx p.x a.val, newRy p.x p.y p.fee a.val, p.fee,
    by dsimp [newRx]; linarith [p.x_pos, a.property],
    newRy_pos _ _ _ _ p.x_pos p.y_pos p.fee_pos a.property, p.fee_pos, p.fee_le⟩,
   ⟨swapOutputY p.x p.y p.fee a.val,
    output_pos _ _ _ _ p.x_pos p.y_pos p.fee_pos a.property⟩)

theorem swap_product (p : Pool) (a : Amount) : product p ≤ product (swap p a).1 :=
  invariant_monotone_with_fee _ _ _ _ p.x_pos p.y_pos p.fee_pos p.fee_le a.property

theorem flip_product (p : Pool) : product (flip p) = product p := mul_comm p.y p.x

def trade (p : Pool) (a : Amount) (reverse : Bool) : Pool × Amount :=
  if reverse then let r := swap (flip p) a; (flip r.1, r.2) else swap p a

theorem trade_product (p : Pool) (a : Amount) (reverse : Bool) :
    product p ≤ product (trade p a reverse).1 := by
  cases reverse with
  | false => exact swap_product p a
  | true =>
    change product p ≤ product (flip (swap (flip p) a).1)
    rw [flip_product, ← flip_product p]
    exact swap_product (flip p) a

variable {ι : Type} [DecidableEq ι]
abbrev Route (ι : Type) := List (ι × Bool)

def step (s : ι → Pool) (a : Amount) (h : ι × Bool) : (ι → Pool) × Amount :=
  let r := trade (s h.1) a h.2
  (Function.update s h.1 r.1, r.2)

def run (s : ι → Pool) (a : Amount) : Route ι → (ι → Pool) × Amount
  | [] => (s, a)
  | h :: hs => let r := step s a h; run r.1 r.2 hs

theorem step_product (s : ι → Pool) (a : Amount) (h : ι × Bool) (j : ι) :
    product (s j) ≤ product ((step s a h).1 j) := by
  by_cases hj : j = h.1
  · subst j
    simpa [step] using trade_product (s h.1) a h.2
  · simp [step, Function.update_of_ne hj]

theorem route_product (s : ι → Pool) (a : Amount) (route : Route ι) (j : ι) :
    product (s j) ≤ product ((run s a route).1 j) := by
  induction route generalizing s a with
  | nil => exact le_rfl
  | cons h hs ih => exact (step_product s a h j).trans (ih (step s a h).1 (step s a h).2)

theorem untouched_pool (s : ι → Pool) (a : Amount) (route : Route ι) (j : ι)
    (hj : ∀ h ∈ route, h.1 ≠ j) : (run s a route).1 j = s j := by
  induction route generalizing s a with
  | nil => rfl
  | cons h hs ih =>
    change (run (step s a h).1 (step s a h).2 hs).1 j = s j
    rw [ih _ _ (fun k hk => hj k (by simp [hk]))]
    exact Function.update_of_ne (Ne.symm (hj h (by simp))) _ _

theorem route_output_positive (s : ι → Pool) (a : Amount) (route : Route ι) :
    0 < (run s a route).2.val := (run s a route).2.property

structure DeFiStatefulAMMRoutingSuite : Prop where
  reserve_invariant : ∀ (ι : Type) [DecidableEq ι] (s : ι → Pool) (a : Amount)
    (route : Route ι) (j : ι), product (s j) ≤ product ((run s a route).1 j)
  frame : ∀ (ι : Type) [DecidableEq ι] (s : ι → Pool) (a : Amount)
    (route : Route ι) (j : ι), (∀ h ∈ route, h.1 ≠ j) → (run s a route).1 j = s j

theorem verification_suite : DeFiStatefulAMMRoutingSuite where
  reserve_invariant := fun _ _ s a route j => route_product s a route j
  frame := fun _ _ s a route j hj => untouched_pool s a route j hj
end DeFiStatefulAMMRouting

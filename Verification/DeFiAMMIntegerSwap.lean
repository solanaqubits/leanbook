/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Tactic

/-! Exact natural-number swap arithmetic with a rational fee multiplier.
Unbounded naturals exclude machine-word overflow; zero-output dust is permitted. -/
namespace DeFiAMMIntegerSwap

def denominator (x d f dx : ℕ) : ℕ := d * x + f * dx

def output (x y d f dx : ℕ) : ℕ := y * (f * dx) / denominator x d f dx

theorem denominator_positive {x d f dx : ℕ} (hx : 0 < x) (hd : 0 < d) :
    0 < denominator x d f dx := by unfold denominator; positivity

theorem rounding_bounds {x y d f dx : ℕ} (hx : 0 < x) (hd : 0 < d) :
    output x y d f dx * denominator x d f dx ≤ y * (f * dx) ∧
    y * (f * dx) < (output x y d f dx + 1) * denominator x d f dx := by
  have hp := denominator_positive (f := f) (dx := dx) hx hd
  exact ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)⟩

theorem output_lt_reserve {x y d f dx : ℕ} (hx : 0 < x) (hy : 0 < y) (hd : 0 < d) :
    output x y d f dx < y := by
  apply (Nat.div_lt_iff_lt_mul (denominator_positive hx hd)).mpr
  unfold denominator
  nlinarith [Nat.mul_pos hy (Nat.mul_pos hd hx)]

theorem reserve_product_nondecreasing {x y d f dx : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hd : 0 < d) (hf : f ≤ d) :
    x * y ≤ (x + dx) * (y - output x y d f dx) := by
  let o := output x y d f dx
  have ho : o ≤ y := (output_lt_reserve hx hy hd).le
  have hs : y - o + o = y := Nat.sub_add_cancel ho
  have hb := (rounding_bounds (y := y) (f := f) (dx := dx) hx hd).1
  change o * (d * x + f * dx) ≤ y * (f * dx) at hb
  conv at hb => rhs; rw [← hs]
  have hm := Nat.mul_le_mul_right ((y - o) * dx) hf
  have h : d * (x * y) ≤ d * ((x + dx) * (y - o)) := by
    conv => lhs; rw [← hs]
    nlinarith
  exact (mul_le_mul_iff_right₀ hd).mp (by simpa only [mul_comm d] using h)

theorem dust_iff {x y d f dx : ℕ} (hx : 0 < x) (hd : 0 < d) :
    output x y d f dx = 0 ↔ y * (f * dx) < denominator x d f dx :=
  by simp only [output, Nat.div_eq_zero_iff,
    ne_of_gt (denominator_positive (f := f) (dx := dx) hx hd), false_or]

theorem zero_input (x y d f : ℕ) : output x y d f 0 = 0 := by simp [output]

structure DeFiAMMIntegerSwapSuite : Prop where
  invariant : ∀ (x y d f dx : ℕ), 0 < x → 0 < y → 0 < d → f ≤ d →
    x * y ≤ (x + dx) * (y - output x y d f dx)
  bound : ∀ (x y d f dx : ℕ), 0 < x → 0 < y → 0 < d → output x y d f dx < y

theorem verification_suite : DeFiAMMIntegerSwapSuite where
  invariant := fun _ _ _ _ _ hx hy hd hf => reserve_product_nondecreasing hx hy hd hf
  bound := fun _ _ _ _ _ hx hy hd => output_lt_reserve hx hy hd
end DeFiAMMIntegerSwap

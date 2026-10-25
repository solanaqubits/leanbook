/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DeFiAMMInvariants

/-! Exact-output inversion and minimal input in the real-valued constant-product model.
Token integer rounding and deployed contract behavior are separate obligations. -/
noncomputable section
open DeFiAMMInvariants
namespace DeFiAMMExactOutput

def requiredInput (rx ry γ dy : ℝ) : ℝ := rx * dy / (γ * (ry - dy))

theorem required_positive {rx ry γ dy : ℝ} (hx : 0 < rx) (hg : 0 < γ)
    (hy : 0 < dy) (hcap : dy < ry) : 0 < requiredInput rx ry γ dy := by
  unfold requiredInput
  exact div_pos (mul_pos hx hy) (mul_pos hg (sub_pos.mpr hcap))

theorem output_of_required {rx ry γ dy : ℝ} (hx : 0 < rx) (hg : 0 < γ)
    (hy : 0 < dy) (hcap : dy < ry) :
    swapOutputY rx ry γ (requiredInput rx ry γ dy) = dy := by
  have hr : 0 < ry := hy.trans hcap
  have hd := sub_pos.mpr hcap
  unfold swapOutputY requiredInput
  field_simp
  ring

theorem required_of_output {rx ry γ dx : ℝ} (hx : 0 < rx) (hr : 0 < ry)
    (hg : 0 < γ) (hdx : 0 < dx) :
    requiredInput rx ry γ (swapOutputY rx ry γ dx) = dx := by
  have hy := output_pos rx ry γ dx hx hr hg hdx
  have hcap := output_lt_reserve rx ry γ dx hx hr hg hdx
  have hc := output_of_required hx hg hy hcap
  have hp := required_positive hx hg hy hcap
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have := output_strictly_monotonic rx ry γ _ _ hx hr hg hp h
    linarith
  · have := output_strictly_monotonic rx ry γ _ _ hx hr hg hdx h
    linarith

theorem minimum_input_iff {rx ry γ dy dx : ℝ} (hx : 0 < rx) (hg : 0 < γ)
    (hy : 0 < dy) (hcap : dy < ry) (hdx : 0 < dx) :
    dy ≤ swapOutputY rx ry γ dx ↔ requiredInput rx ry γ dy ≤ dx := by
  have hr := hy.trans hcap
  have hp := required_positive hx hg hy hcap
  have he := output_of_required hx hg hy hcap
  constructor
  · intro h
    by_contra hn
    have hc := output_strictly_monotonic rx ry γ _ _ hx hr hg hdx (lt_of_not_ge hn)
    linarith
  · intro h
    rcases h.eq_or_lt with heq | hlt
    · simpa [← heq] using he.ge
    · have hc := output_strictly_monotonic rx ry γ _ _ hx hr hg hp hlt
      linarith

theorem exact_input_unique {rx ry γ dy dx : ℝ} (hx : 0 < rx) (hg : 0 < γ)
    (hy : 0 < dy) (hcap : dy < ry) (hdx : 0 < dx)
    (he : swapOutputY rx ry γ dx = dy) : dx = requiredInput rx ry γ dy := by
  rw [← he, required_of_output hx (hy.trans hcap) hg hdx]

structure DeFiAMMExactOutputSuite : Prop where
  inversion : ∀ (rx ry γ dy : ℝ), 0 < rx → 0 < γ → 0 < dy → dy < ry →
    swapOutputY rx ry γ (requiredInput rx ry γ dy) = dy
  minimal : ∀ (rx ry γ dy dx : ℝ), 0 < rx → 0 < γ → 0 < dy → dy < ry → 0 < dx →
    (dy ≤ swapOutputY rx ry γ dx ↔ requiredInput rx ry γ dy ≤ dx)

theorem verification_suite : DeFiAMMExactOutputSuite where
  inversion := fun _ _ _ _ hx hg hy hc => output_of_required hx hg hy hc
  minimal := fun _ _ _ _ _ hx hg hy hc hd => minimum_input_iff hx hg hy hc hd
end DeFiAMMExactOutput

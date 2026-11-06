/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyVisibility
import Mathlib.Analysis.SpecificLimits.Basic

/-! Scalar consequences of the specified Werner transition. The separate operator
bridge is in QuantumWernerCascade. No general CPTP fidelity monotonicity is claimed. -/
noncomputable section
namespace QuantumCascadeReduction
open QuantumCentralDepolarization QuantumNoisyVisibility
open Filter
open scoped Topology

structure CascadeParameters where
  gamma_corr : ℝ
  gamma_bsm : ℝ
  w_fresh : ℝ
  h_gc_pos : 0 ≤ gamma_corr
  h_gc_le : gamma_corr ≤ 1
  h_gb_pos : 0 ≤ gamma_bsm
  h_gb_le : gamma_bsm ≤ 1
  h_wf_pos : 0 ≤ w_fresh
  h_wf_le : w_fresh ≤ 1

def ofVisibilities (bsm corr fresh : Visibility) : CascadeParameters :=
  ⟨corr.val, bsm.val, fresh.val, corr.nonnegative, corr.le_one,
    bsm.nonnegative, bsm.le_one, fresh.nonnegative, fresh.le_one⟩

def alphaParam (p : CascadeParameters) : ℝ := p.gamma_corr * p.gamma_bsm * p.w_fresh

def wernerTransition (p : CascadeParameters) (w : ℝ) : ℝ := alphaParam p * w

def wernerFidelity (w : ℝ) : ℝ := (1 + 3 * w) / 4

theorem alpha_bounds (p : CascadeParameters) : 0 ≤ alphaParam p ∧ alphaParam p ≤ 1 := by
  have hprod := mul_le_mul p.h_gc_le p.h_gb_le p.h_gb_pos (by norm_num : (0 : ℝ) ≤ 1)
  have hprod0 := mul_nonneg p.h_gc_pos p.h_gb_pos
  constructor
  · exact mul_nonneg hprod0 p.h_wf_pos
  · have h := mul_le_mul hprod p.h_wf_le p.h_wf_pos (by norm_num : (0 : ℝ) ≤ 1 * 1)
    simpa only [alphaParam, one_mul] using h

/-- The upper bound w ≤ 1 is not needed for nonincrease. -/
theorem werner_transition_le_id (p : CascadeParameters) (w : ℝ) (hw : 0 ≤ w) :
    wernerTransition p w ≤ w := by
  simpa only [wernerTransition, one_mul] using mul_le_mul_of_nonneg_right (alpha_bounds p).2 hw

theorem transition_bounds (p : CascadeParameters) (w : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 ≤ wernerTransition p w ∧ wernerTransition p w ≤ 1 :=
  ⟨mul_nonneg (alpha_bounds p).1 hw.1, (werner_transition_le_id p w hw.1).trans hw.2⟩

theorem fidelity_monotonicity (p : CascadeParameters) (w : ℝ) (hw : 0 ≤ w) :
    wernerFidelity (wernerTransition p w) ≤ wernerFidelity w := by
  have h := werner_transition_le_id p w hw
  unfold wernerFidelity
  linarith

/-- Strict loss needs both positive input visibility and a strictly lossy multiplier. -/
theorem strict_decay (p : CascadeParameters) (w : ℝ) (hw : 0 < w)
    (ha : alphaParam p < 1) :
    wernerTransition p w < w ∧ wernerFidelity (wernerTransition p w) < wernerFidelity w := by
  have h : wernerTransition p w < w := by
    simpa only [wernerTransition, one_mul] using mul_lt_mul_of_pos_right ha hw
  exact ⟨h, by unfold wernerFidelity; linarith⟩

theorem fixed_point_iff (p : CascadeParameters) (w : ℝ) :
    wernerTransition p w = w ↔ w = 0 ∨ alphaParam p = 1 := by
  constructor
  · intro h
    have hz : w * (alphaParam p - 1) = 0 := by unfold wernerTransition at h; nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  · rintro (h | h) <;> simp [wernerTransition, h]

theorem unique_fixed_point_at_zero (p : CascadeParameters) (w : ℝ)
    (ha : alphaParam p < 1) : wernerTransition p w = w ↔ w = 0 := by
  rw [fixed_point_iff, or_iff_left (ne_of_lt ha)]

theorem lossless_identity (p : CascadeParameters) (ha : alphaParam p = 1) (w : ℝ) :
    wernerTransition p w = w := by simp [wernerTransition, ha]

theorem fidelity_equality_iff (p : CascadeParameters) (w : ℝ) :
    wernerFidelity (wernerTransition p w) = wernerFidelity w ↔
      w = 0 ∨ alphaParam p = 1 := by
  rw [← fixed_point_iff]
  unfold wernerFidelity
  constructor <;> intro h <;> linarith

theorem cascaded_iteration (p : CascadeParameters) (w : ℝ) (n : ℕ) :
    (wernerTransition p)^[n] w = alphaParam p ^ n * w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [wernerTransition, pow_succ]
    ring

/-- Chronological finite schedule; its multipliers may vary from round to round. -/
def runVisibility : List CascadeParameters → ℝ → ℝ
  | [], w => w
  | p :: ps, w => runVisibility ps (wernerTransition p w)

theorem finite_schedule_product (ps : List CascadeParameters) (w : ℝ) :
    runVisibility ps w = (ps.map alphaParam).prod * w := by
  induction ps generalizing w with
  | nil => simp [runVisibility]
  | cons p ps ih =>
    simp only [runVisibility, ih, List.map_cons, List.prod_cons, wernerTransition]
    ring

/-- Actual convergence, separately from the finite-iteration identity. -/
theorem visibility_tends_to_zero (p : CascadeParameters) (ha : alphaParam p < 1) (w : ℝ) :
    Tendsto (fun n : ℕ => (wernerTransition p)^[n] w) atTop (𝓝 0) := by
  simpa only [cascaded_iteration, zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (alpha_bounds p).1 ha).mul_const w

theorem fidelity_tends_to_quarter (p : CascadeParameters) (ha : alphaParam p < 1) (w : ℝ) :
    Tendsto (fun n : ℕ => wernerFidelity ((wernerTransition p)^[n] w)) atTop (𝓝 (1/4)) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
    ((visibility_tends_to_zero p ha w).const_mul 3)).div_const 4
  simpa only [mul_zero, add_zero, wernerFidelity] using h

/-- For nonnegative visibility the approach is from above, possibly reaching 1/4 immediately. -/
theorem fidelity_above_quarter (p : CascadeParameters) (w : ℝ) (hw : 0 ≤ w) (n : ℕ) :
    (1/4 : ℝ) ≤ wernerFidelity ((wernerTransition p)^[n] w) := by
  rw [cascaded_iteration]
  have h := mul_nonneg (pow_nonneg (alpha_bounds p).1 n) hw
  unfold wernerFidelity
  linarith

/-- A varying schedule need not decay: uniform strict contraction is not assumed. -/
theorem finite_schedule_nonincrease (ps : List CascadeParameters) (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ runVisibility ps w ∧ runVisibility ps w ≤ w := by
  induction ps generalizing w with
  | nil => exact ⟨hw, le_rfl⟩
  | cons p ps ih =>
    have ht := mul_nonneg (alpha_bounds p).1 hw
    have h := ih (wernerTransition p w) ht
    exact ⟨h.1, h.2.trans (werner_transition_le_id p w hw)⟩

structure QuantumCascadeReductionSuite : Prop where
  bounds : ∀ p, 0 ≤ alphaParam p ∧ alphaParam p ≤ 1
  fixed : ∀ p w, wernerTransition p w = w ↔ w = 0 ∨ alphaParam p = 1
  iteration : ∀ p w n, (wernerTransition p)^[n] w = alphaParam p ^ n * w
  limit : ∀ p, alphaParam p < 1 → ∀ w,
    Tendsto (fun n : ℕ => wernerFidelity ((wernerTransition p)^[n] w)) atTop (𝓝 (1/4))

theorem verification_suite : QuantumCascadeReductionSuite :=
  ⟨alpha_bounds, fixed_point_iff, cascaded_iteration, fidelity_tends_to_quarter⟩

end QuantumCascadeReduction

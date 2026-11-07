/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyBBPSSW

/-! Basins of the constant-quality, supercritical post-depolarized BBPSSW map.
The lower fixed point separates two basins; limits are not selected by distance.
No variable noise schedule, convergence rate or resource yield is modeled. -/
noncomputable section
namespace QuantumNoisyBBPSSWConvergence
open QuantumNoisyBBPSSW QuantumBBPSSWDistillation QuantumBBPSSWConvergence
open Filter Topology

def noisyOrbit (γ F : ℝ) (n : ℕ) : ℝ := ((noisyRecurrence γ)^[n]) F

@[simp] theorem noisyOrbit_zero (γ F : ℝ) : noisyOrbit γ F 0 = F := rfl

theorem noisyOrbit_succ (γ F : ℝ) (n : ℕ) :
    noisyOrbit γ F (n + 1) = noisyRecurrence γ (noisyOrbit γ F n) :=
  Function.iterate_succ_apply' _ _ _

theorem noisyOrbit_fixed {γ F : ℝ} (h : noisyRecurrence γ F = F) (n : ℕ) :
    noisyOrbit γ F n = F := by
  induction n with
  | zero => rfl
  | succ n ih => rw [noisyOrbit_succ, ih, h]

theorem noisyOrbit_stationary_iff {γ F : ℝ} (hc : criticalGamma < γ) :
    (∀ n, noisyOrbit γ F n = F) ↔
      F = 1 / 4 ∨ F = lowerWindowBound γ ∨ F = upperWindowCeiling γ := by
  constructor
  · intro h
    apply (noisyRecurrence_fixed_points_iff hc).mp
    simpa [noisyOrbit_succ] using h 1
  · intro h
    exact noisyOrbit_fixed ((noisyRecurrence_fixed_points_iff hc).mpr h)

theorem noisyOrbit_bounds {γ F : ℝ} (hg : 0 ≤ γ ∧ γ ≤ 1) (hF : 0 ≤ F ∧ F ≤ 1)
    (n : ℕ) : 0 ≤ noisyOrbit γ F n ∧ noisyOrbit γ F n ≤ 1 := by
  induction n with
  | zero => exact hF
  | succ n ih => rw [noisyOrbit_succ]; exact noisyRecurrence_bounds hg.1 hg.2 ih.1 ih.2

theorem continuous_noisyRecurrence (γ : ℝ) : Continuous (noisyRecurrence γ) :=
  continuous_const.add (continuous_const.mul continuous_recurrence)

theorem noisyOrbit_limit_is_fixed_point {γ F L : ℝ}
    (h : Tendsto (noisyOrbit γ F) atTop (nhds L)) : noisyRecurrence γ L = L := by
  have hs : Tendsto (fun n => noisyOrbit γ F (n + 1)) atTop (nhds L) :=
    (tendsto_add_atTop_iff_nat 1).mpr h
  have hc := (continuous_noisyRecurrence γ).continuousAt.tendsto.comp h
  simp only [noisyOrbit_succ] at hs
  exact tendsto_nhds_unique hc hs

/-- This low-fidelity barrier uses the ideal factorization, not input monotonicity below 1 / 4. -/
theorem noisy_step_below_quarter {γ F : ℝ}
    (hγ : 0 < γ) (hγ1 : γ < 1) (h0 : 0 ≤ F) (hq : F < 1 / 4) :
    F < noisyRecurrence γ F ∧ noisyRecurrence γ F < 1 / 4 := by
  have hr := recurrence_invariant_below_quarter h0 hq
  have hi := improves_below_quarter F hq
  have hp := mul_pos hγ (sub_pos.mpr hi)
  have hqmul := mul_pos (show 0 < 1 - γ by linarith) (show 0 < 1 / 4 - F by linarith)
  have hu := mul_pos hγ (show 0 < 1 / 4 - recurrence F by linarith)
  unfold noisyRecurrence
  constructor <;> nlinarith

/-- Strict decay on either side of the open working window, above the mixing fixed point. -/
theorem noisy_step_decay_outside_window {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1) (hF : 1 / 4 < F)
    (hout : F < lowerWindowBound γ ∨ upperWindowCeiling γ < F) :
    noisyRecurrence γ F < F := by
  have hb := working_window_inside_half_one hc h1
  have hp : 0 < (F - lowerWindowBound γ) * (F - upperWindowCeiling γ) := by
    rcases hout with hl | hu
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith [hb.2.1])
    · exact mul_pos (by linarith [hb.2.1]) (by linarith)
  have hq : noisyIncrementQuad γ F < 0 := by
    rw [noisyIncrementQuad_roots (noisyDiscFactor_pos hc).le]
    nlinarith
  have hi : noisyRecurrence γ F - F < 0 := by
    rw [noisyRecurrence_sub_self]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) hq)
      (mul_pos (by norm_num) (probability_positive F))
  linarith

theorem noisy_step_between_quarter_and_lower {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : 1 / 4 < F) (hhi : F < lowerWindowBound γ) :
    1 / 4 < noisyRecurrence γ F ∧ noisyRecurrence γ F < F := by
  have hb := working_window_inside_half_one hc h1
  have hg : 0 < γ := by linarith [criticalGamma_bounds.1]
  have hmono := noisyRecurrence_strictMonoOn hg
    (show (1 / 4 : ℝ) ∈ Set.Icc (1 / 4) 1 by norm_num)
    (show F ∈ Set.Icc (1 / 4 : ℝ) 1 by exact ⟨hlo.le, by linarith [hb.2.1, hb.2.2]⟩) hlo
  rw [noisyRecurrence_quarter] at hmono
  exact ⟨hmono, noisy_step_decay_outside_window hc h1 hlo (Or.inl hhi)⟩

theorem noisy_step_inside_window {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : lowerWindowBound γ < F) (hhi : F < upperWindowCeiling γ) :
    F < noisyRecurrence γ F ∧ noisyRecurrence γ F < upperWindowCeiling γ := by
  have hb := working_window_inside_half_one hc h1
  have hg : 0 < γ := by linarith [criticalGamma_bounds.1]
  have hf : noisyRecurrence γ (upperWindowCeiling γ) = upperWindowCeiling γ :=
    (noisyRecurrence_fixed_points_iff hc).mpr (Or.inr (Or.inr rfl))
  have hmono := noisyRecurrence_strictMonoOn hg
    (show F ∈ Set.Icc (1 / 4 : ℝ) 1 by exact ⟨by linarith [hb.1], by linarith [hb.2.2]⟩)
    (show upperWindowCeiling γ ∈ Set.Icc (1 / 4 : ℝ) 1 by
      exact ⟨by linarith [hb.1, hb.2.1], hb.2.2.le⟩) hhi
  rw [hf] at hmono
  exact ⟨(noisyRecurrence_strict_improve_iff_in_window hc h1 (by linarith [hb.1])).mpr
    ⟨hlo, hhi⟩, hmono⟩

theorem noisy_step_above_ceiling {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : upperWindowCeiling γ < F) (hhi : F ≤ 1) :
    upperWindowCeiling γ < noisyRecurrence γ F ∧ noisyRecurrence γ F < F := by
  have hb := working_window_inside_half_one hc h1
  have hg : 0 < γ := by linarith [criticalGamma_bounds.1]
  have hf : noisyRecurrence γ (upperWindowCeiling γ) = upperWindowCeiling γ :=
    (noisyRecurrence_fixed_points_iff hc).mpr (Or.inr (Or.inr rfl))
  have hmono := noisyRecurrence_strictMonoOn hg
    (show upperWindowCeiling γ ∈ Set.Icc (1 / 4 : ℝ) 1 by
      exact ⟨by linarith [hb.1, hb.2.1], hb.2.2.le⟩)
    (show F ∈ Set.Icc (1 / 4 : ℝ) 1 by exact ⟨by linarith [hb.1, hb.2.1], hhi⟩) hlo
  rw [hf] at hmono
  exact ⟨hmono, noisy_step_decay_outside_window hc h1
    (by linarith [hb.1, hb.2.1]) (Or.inr hlo)⟩

/-- Invariance is quantified at every index, including the initial index zero. -/
theorem noisyOrbit_below_quarter {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1) (h0 : 0 ≤ F) (hq : F < 1 / 4) (n : ℕ) :
    0 ≤ noisyOrbit γ F n ∧ noisyOrbit γ F n < 1 / 4 := by
  induction n with
  | zero => exact ⟨h0, hq⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have h := noisy_step_below_quarter (by linarith [criticalGamma_bounds.1]) h1 ih.1 ih.2
    exact ⟨by linarith, h.2⟩

theorem noisyOrbit_between_quarter_and_lower {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : 1 / 4 < F) (hhi : F < lowerWindowBound γ) (n : ℕ) :
    1 / 4 < noisyOrbit γ F n ∧ noisyOrbit γ F n < lowerWindowBound γ := by
  induction n with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have h := noisy_step_between_quarter_and_lower hc h1 ih.1 ih.2
    exact ⟨h.1, lt_trans h.2 ih.2⟩

theorem noisyOrbit_inside_window {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : lowerWindowBound γ < F) (hhi : F < upperWindowCeiling γ) (n : ℕ) :
    lowerWindowBound γ < noisyOrbit γ F n ∧ noisyOrbit γ F n < upperWindowCeiling γ := by
  induction n with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have h := noisy_step_inside_window hc h1 ih.1 ih.2
    exact ⟨lt_trans ih.1 h.1, h.2⟩

theorem noisyOrbit_above_ceiling {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : upperWindowCeiling γ < F) (hhi : F ≤ 1) (n : ℕ) :
    upperWindowCeiling γ < noisyOrbit γ F n ∧ noisyOrbit γ F n ≤ 1 := by
  induction n with
  | zero => exact ⟨hlo, hhi⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have h := noisy_step_above_ceiling hc h1 ih.1 ih.2
    exact ⟨h.1, le_trans h.2.le ih.2⟩

theorem noisyOrbit_strictMono_below_quarter {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1) (h0 : 0 ≤ F) (hq : F < 1 / 4) :
    StrictMono (noisyOrbit γ F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [noisyOrbit_succ]
  have h := noisyOrbit_below_quarter hc h1 h0 hq n
  exact (noisy_step_below_quarter (by linarith [criticalGamma_bounds.1]) h1 h.1 h.2).1

theorem noisyOrbit_strictAnti_between_quarter_and_lower {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : 1 / 4 < F) (hhi : F < lowerWindowBound γ) : StrictAnti (noisyOrbit γ F) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [noisyOrbit_succ]
  have h := noisyOrbit_between_quarter_and_lower hc h1 hlo hhi n
  exact (noisy_step_between_quarter_and_lower hc h1 h.1 h.2).2

theorem noisyOrbit_strictMono_inside_window {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : lowerWindowBound γ < F) (hhi : F < upperWindowCeiling γ) :
    StrictMono (noisyOrbit γ F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [noisyOrbit_succ]
  have h := noisyOrbit_inside_window hc h1 hlo hhi n
  exact (noisy_step_inside_window hc h1 h.1 h.2).1

theorem noisyOrbit_strictAnti_above_ceiling {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : upperWindowCeiling γ < F) (hhi : F ≤ 1) : StrictAnti (noisyOrbit γ F) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [noisyOrbit_succ]
  have h := noisyOrbit_above_ceiling hc h1 hlo hhi n
  exact (noisy_step_above_ceiling hc h1 h.1 h.2).2

/-- The unstable lower root is excluded by the initial-value barrier, not by proximity. -/
theorem noisyOrbit_tendsto_quarter {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1) (h0 : 0 ≤ F) (hlo : F < lowerWindowBound γ) :
    Tendsto (noisyOrbit γ F) atTop (nhds (1 / 4)) := by
  have hb := working_window_inside_half_one hc h1
  rcases lt_trichotomy F (1 / 4) with hq | he | hq
  · have hm := (noisyOrbit_strictMono_below_quarter hc h1 h0 hq).monotone
    have hbound : BddAbove (Set.range (noisyOrbit γ F)) :=
      ⟨1 / 4, by rintro _ ⟨n, rfl⟩; exact (noisyOrbit_below_quarter hc h1 h0 hq n).2.le⟩
    have ht := tendsto_atTop_ciSup hm hbound
    have hu : (⨆ n, noisyOrbit γ F n) ≤ 1 / 4 :=
      ciSup_le (fun n => (noisyOrbit_below_quarter hc h1 h0 hq n).2.le)
    rcases (noisyRecurrence_fixed_points_iff hc).mp
      (noisyOrbit_limit_is_fixed_point ht) with hq' | hl | hu'
    · rwa [hq'] at ht
    · linarith [hb.1]
    · linarith [hb.1, hb.2.1]
  · subst F
    have he : noisyOrbit γ (1 / 4) = fun _ => (1 / 4 : ℝ) :=
      funext (noisyOrbit_fixed (noisyRecurrence_quarter γ))
    rw [he]
    exact tendsto_const_nhds
  · have hm := (noisyOrbit_strictAnti_between_quarter_and_lower hc h1 hq hlo).antitone
    have hbound : BddBelow (Set.range (noisyOrbit γ F)) :=
      ⟨1 / 4, by
        rintro _ ⟨n, rfl⟩
        exact (noisyOrbit_between_quarter_and_lower hc h1 hq hlo n).1.le⟩
    have ht := tendsto_atTop_ciInf hm hbound
    have hu : (⨅ n, noisyOrbit γ F n) ≤ F := by simpa using ciInf_le hbound 0
    rcases (noisyRecurrence_fixed_points_iff hc).mp
      (noisyOrbit_limit_is_fixed_point ht) with hq' | hl | hu'
    · rwa [hq'] at ht
    · linarith
    · linarith [hb.2.1]

/-- Attraction to the upper stationary ceiling from both sides, including a pure initial pair. -/
theorem noisyOrbit_tendsto_ceiling {γ F : ℝ}
    (hc : criticalGamma < γ) (h1 : γ < 1)
    (hlo : lowerWindowBound γ < F) (hhi : F ≤ 1) :
    Tendsto (noisyOrbit γ F) atTop (nhds (upperWindowCeiling γ)) := by
  have hb := working_window_inside_half_one hc h1
  rcases lt_trichotomy F (upperWindowCeiling γ) with hu | he | hu
  · have hm := (noisyOrbit_strictMono_inside_window hc h1 hlo hu).monotone
    have hbound : BddAbove (Set.range (noisyOrbit γ F)) :=
      ⟨upperWindowCeiling γ, by
        rintro _ ⟨n, rfl⟩
        exact (noisyOrbit_inside_window hc h1 hlo hu n).2.le⟩
    have ht := tendsto_atTop_ciSup hm hbound
    have hl : F ≤ ⨆ n, noisyOrbit γ F n := by simpa using le_ciSup hbound 0
    rcases (noisyRecurrence_fixed_points_iff hc).mp
      (noisyOrbit_limit_is_fixed_point ht) with hq | hl' | hu'
    · linarith [hb.1]
    · linarith
    · rwa [hu'] at ht
  · subst F
    have hf : noisyRecurrence γ (upperWindowCeiling γ) = upperWindowCeiling γ :=
      (noisyRecurrence_fixed_points_iff hc).mpr (Or.inr (Or.inr rfl))
    have he : noisyOrbit γ (upperWindowCeiling γ) = fun _ => upperWindowCeiling γ :=
      funext (noisyOrbit_fixed hf)
    rw [he]
    exact tendsto_const_nhds
  · have hm := (noisyOrbit_strictAnti_above_ceiling hc h1 hu hhi).antitone
    have hbound : BddBelow (Set.range (noisyOrbit γ F)) :=
      ⟨upperWindowCeiling γ, by
        rintro _ ⟨n, rfl⟩
        exact (noisyOrbit_above_ceiling hc h1 hu hhi n).1.le⟩
    have ht := tendsto_atTop_ciInf hm hbound
    have hl : upperWindowCeiling γ ≤ ⨅ n, noisyOrbit γ F n :=
      le_ciInf (fun n => (noisyOrbit_above_ceiling hc h1 hu hhi n).1.le)
    rcases (noisyRecurrence_fixed_points_iff hc).mp
      (noisyOrbit_limit_is_fixed_point ht) with hq | hl' | hu'
    · linarith [hb.1, hb.2.1]
    · linarith [hb.2.1]
    · rwa [hu'] at ht

structure QuantumNoisyBBPSSWConvergenceSuite : Prop where
  mixing : ∀ γ F, criticalGamma < γ → γ < 1 → 0 ≤ F → F < lowerWindowBound γ →
    Tendsto (noisyOrbit γ F) atTop (nhds (1 / 4))
  purification : ∀ γ F, criticalGamma < γ → γ < 1 → lowerWindowBound γ < F → F ≤ 1 →
    Tendsto (noisyOrbit γ F) atTop (nhds (upperWindowCeiling γ))
  stationary : ∀ γ F, criticalGamma < γ →
    ((∀ n, noisyOrbit γ F n = F) ↔
      F = 1 / 4 ∨ F = lowerWindowBound γ ∨ F = upperWindowCeiling γ)

theorem verification_suite : QuantumNoisyBBPSSWConvergenceSuite :=
  ⟨fun _ _ => noisyOrbit_tendsto_quarter, fun _ _ => noisyOrbit_tendsto_ceiling,
    fun _ _ => noisyOrbit_stationary_iff⟩

end QuantumNoisyBBPSSWConvergence

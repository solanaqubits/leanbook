/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyBBPSSWConvergence

/-! Critical and subcritical constant-quality noisy BBPSSW orbits.
The critical double root attracts from above; points below it tend to mixing.
The zero-quality channel reaches mixing by the first step, with no strict orbit monotonicity. -/
noncomputable section
namespace QuantumNoisyBBPSSWCritical
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence QuantumBBPSSWDistillation
open Filter Topology

def criticalFidelity : ℝ := (2 * criticalGamma + 1) / 4

theorem criticalFidelity_radical : criticalFidelity = (3 * Real.sqrt 5 - 1) / 8 := by
  unfold criticalFidelity criticalGamma
  ring

theorem criticalFidelity_bounds : 1 / 2 < criticalFidelity ∧ criticalFidelity < 1 := by
  unfold criticalFidelity
  constructor <;> linarith [criticalGamma_bounds.1, criticalGamma_bounds.2]

/-- The fixed-point classification holds on the entire real line. -/
theorem critical_fixed_iff (F : ℝ) :
    noisyRecurrence criticalGamma F = F ↔ F = 1 / 4 ∨ F = criticalFidelity :=
  noisyRecurrence_critical_fixed_iff F

theorem critical_stationary_iff (F : ℝ) :
    (∀ n, noisyOrbit criticalGamma F n = F) ↔ F = 1 / 4 ∨ F = criticalFidelity := by
  constructor
  · intro h
    apply (critical_fixed_iff F).mp
    simpa [noisyOrbit_succ] using h 1
  · intro h
    exact noisyOrbit_fixed ((critical_fixed_iff F).mpr h)

theorem critical_increment (F : ℝ) :
    noisyRecurrence criticalGamma F - F =
      -(2 * (4 * F - 1) * (F - criticalFidelity) ^ 2) / (9 * successProbability F) := by
  rw [noisyRecurrence_sub_self, noisyIncrementQuad_critical]
  unfold criticalFidelity
  ring

theorem critical_strict_decay {F : ℝ} (hq : 1 / 4 < F) (hne : F ≠ criticalFidelity) :
    noisyRecurrence criticalGamma F < F := by
  rcases (noisyRecurrence_critical_no_strict_gain hq.le).eq_or_lt with he | he
  · rcases (critical_fixed_iff F).mp he with h | h
    · linarith
    · exact (hne h).elim
  · exact he

/-- Above mixing, strict input monotonicity supplies a barrier for any positive quality. -/
theorem noisy_step_above_quarter {γ F : ℝ} (hg : 0 < γ)
    (hq : 1 / 4 < F) (h1 : F ≤ 1) : 1 / 4 < noisyRecurrence γ F := by
  have h := noisyRecurrence_strictMonoOn hg
    (show (1 / 4 : ℝ) ∈ Set.Icc (1 / 4) 1 by norm_num) ⟨hq.le, h1⟩ hq
  rwa [noisyRecurrence_quarter] at h

/-- These low-fidelity invariants do not require supercritical quality. -/
theorem lowOrbit_invariant {γ F : ℝ} (hg : 0 < γ) (hg1 : γ < 1)
    (h0 : 0 ≤ F) (hq : F < 1 / 4) (n : ℕ) :
    0 ≤ noisyOrbit γ F n ∧ noisyOrbit γ F n < 1 / 4 := by
  induction n with
  | zero => exact ⟨h0, hq⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have hs := noisy_step_below_quarter hg hg1 ih.1 ih.2
    exact ⟨by linarith, hs.2⟩

theorem lowOrbit_strictMono {γ F : ℝ} (hg : 0 < γ) (hg1 : γ < 1)
    (h0 : 0 ≤ F) (hq : F < 1 / 4) : StrictMono (noisyOrbit γ F) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [noisyOrbit_succ]
  have h := lowOrbit_invariant hg hg1 h0 hq n
  exact (noisy_step_below_quarter hg hg1 h.1 h.2).1

theorem critical_step_below_double {F : ℝ}
    (hq : 1 / 4 < F) (hs : F < criticalFidelity) :
    1 / 4 < noisyRecurrence criticalGamma F ∧ noisyRecurrence criticalGamma F < F := by
  exact ⟨noisy_step_above_quarter (by linarith [criticalGamma_bounds.1]) hq
    (by linarith [criticalFidelity_bounds.2]), critical_strict_decay hq hs.ne⟩

theorem critical_step_above_double {F : ℝ}
    (hs : criticalFidelity < F) (h1 : F ≤ 1) :
    criticalFidelity < noisyRecurrence criticalGamma F ∧
    noisyRecurrence criticalGamma F < F := by
  have hf : noisyRecurrence criticalGamma criticalFidelity = criticalFidelity :=
    (critical_fixed_iff criticalFidelity).mpr (Or.inr rfl)
  have hm := noisyRecurrence_strictMonoOn
    (show 0 < criticalGamma by linarith [criticalGamma_bounds.1])
    ⟨show (1 / 4 : ℝ) ≤ criticalFidelity by linarith [criticalFidelity_bounds.1],
      criticalFidelity_bounds.2.le⟩
    ⟨show (1 / 4 : ℝ) ≤ F by linarith [criticalFidelity_bounds.1], h1⟩ hs
  rw [hf] at hm
  exact ⟨hm, critical_strict_decay (by linarith [criticalFidelity_bounds.1]) hs.ne'⟩

theorem criticalOrbit_below_double {F : ℝ}
    (hq : 1 / 4 < F) (hs : F < criticalFidelity) (n : ℕ) :
    1 / 4 < noisyOrbit criticalGamma F n ∧
    noisyOrbit criticalGamma F n < criticalFidelity := by
  induction n with
  | zero => exact ⟨hq, hs⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have h := critical_step_below_double ih.1 ih.2
    exact ⟨h.1, lt_trans h.2 ih.2⟩

theorem criticalOrbit_above_double {F : ℝ}
    (hs : criticalFidelity < F) (h1 : F ≤ 1) (n : ℕ) :
    criticalFidelity < noisyOrbit criticalGamma F n ∧ noisyOrbit criticalGamma F n ≤ 1 := by
  induction n with
  | zero => exact ⟨hs, h1⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have h := critical_step_above_double ih.1 ih.2
    exact ⟨h.1, le_trans h.2.le ih.2⟩

theorem criticalOrbit_strictAnti_below_double {F : ℝ}
    (hq : 1 / 4 < F) (hs : F < criticalFidelity) :
    StrictAnti (noisyOrbit criticalGamma F) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [noisyOrbit_succ]
  have h := criticalOrbit_below_double hq hs n
  exact (critical_step_below_double h.1 h.2).2

theorem criticalOrbit_strictAnti_above_double {F : ℝ}
    (hs : criticalFidelity < F) (h1 : F ≤ 1) :
    StrictAnti (noisyOrbit criticalGamma F) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [noisyOrbit_succ]
  have h := criticalOrbit_above_double hs h1 n
  exact (critical_step_above_double h.1 h.2).2

/-- Below the double root, the limit is mixing, not the double root. -/
theorem criticalOrbit_tendsto_quarter {F : ℝ} (h0 : 0 ≤ F) (hs : F < criticalFidelity) :
    Tendsto (noisyOrbit criticalGamma F) atTop (nhds (1 / 4)) := by
  have hg : 0 < criticalGamma := by linarith [criticalGamma_bounds.1]
  have hg1 := criticalGamma_bounds.2
  rcases lt_trichotomy F (1 / 4) with hq | he | hq
  · have hm := (lowOrbit_strictMono hg hg1 h0 hq).monotone
    have hb : BddAbove (Set.range (noisyOrbit criticalGamma F)) :=
      ⟨1 / 4, by rintro _ ⟨n, rfl⟩; exact (lowOrbit_invariant hg hg1 h0 hq n).2.le⟩
    have ht := tendsto_atTop_ciSup hm hb
    have hu : (⨆ n, noisyOrbit criticalGamma F n) ≤ 1 / 4 :=
      ciSup_le (fun n => (lowOrbit_invariant hg hg1 h0 hq n).2.le)
    rcases (critical_fixed_iff _).mp (noisyOrbit_limit_is_fixed_point ht) with he | he
    · rwa [he] at ht
    · linarith [criticalFidelity_bounds.1]
  · subst F
    have he : noisyOrbit criticalGamma (1 / 4) = fun _ => (1 / 4 : ℝ) :=
      funext (noisyOrbit_fixed (noisyRecurrence_quarter criticalGamma))
    rw [he]
    exact tendsto_const_nhds
  · have hm := (criticalOrbit_strictAnti_below_double hq hs).antitone
    have hb : BddBelow (Set.range (noisyOrbit criticalGamma F)) :=
      ⟨1 / 4, by
        rintro _ ⟨n, rfl⟩
        exact (criticalOrbit_below_double hq hs n).1.le⟩
    have ht := tendsto_atTop_ciInf hm hb
    have hu : (⨅ n, noisyOrbit criticalGamma F n) ≤ F := by simpa using ciInf_le hb 0
    rcases (critical_fixed_iff _).mp (noisyOrbit_limit_is_fixed_point ht) with he | he
    · rwa [he] at ht
    · linarith

/-- The critical double root attracts from above, including the stationary endpoint. -/
theorem criticalOrbit_tendsto_double {F : ℝ} (hs : criticalFidelity ≤ F) (h1 : F ≤ 1) :
    Tendsto (noisyOrbit criticalGamma F) atTop (nhds criticalFidelity) := by
  rcases hs.eq_or_lt with he | hs
  · subst F
    have hf := (critical_fixed_iff criticalFidelity).mpr (Or.inr rfl)
    have he : noisyOrbit criticalGamma criticalFidelity = fun _ => criticalFidelity :=
      funext (noisyOrbit_fixed hf)
    rw [he]
    exact tendsto_const_nhds
  · have hm := (criticalOrbit_strictAnti_above_double hs h1).antitone
    have hb : BddBelow (Set.range (noisyOrbit criticalGamma F)) :=
      ⟨criticalFidelity, by
        rintro _ ⟨n, rfl⟩
        exact (criticalOrbit_above_double hs h1 n).1.le⟩
    have ht := tendsto_atTop_ciInf hm hb
    have hl : criticalFidelity ≤ ⨅ n, noisyOrbit criticalGamma F n :=
      le_ciInf (fun n => (criticalOrbit_above_double hs h1 n).1.le)
    rcases (critical_fixed_iff _).mp (noisyOrbit_limit_is_fixed_point ht) with he | he
    · linarith [criticalFidelity_bounds.1]
    · rwa [he] at ht

/-- Zero quality is absorbed at mixing after one step, even for arbitrary real input. -/
theorem zeroQuality_orbit_succ (F : ℝ) (n : ℕ) : noisyOrbit 0 F (n + 1) = 1 / 4 := by
  rw [noisyOrbit_succ, noisyRecurrence_zero]

theorem zeroQuality_tendsto (F : ℝ) : Tendsto (noisyOrbit 0 F) atTop (nhds (1 / 4)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have he : (fun n => noisyOrbit 0 F (n + 1)) = fun _ => (1 / 4 : ℝ) :=
    funext (zeroQuality_orbit_succ F)
  rw [he]
  exact tendsto_const_nhds

theorem subcritical_step_above_quarter {γ F : ℝ}
    (hg : 0 < γ) (hc : γ < criticalGamma) (hq : 1 / 4 < F) (h1 : F ≤ 1) :
    1 / 4 < noisyRecurrence γ F ∧ noisyRecurrence γ F < F :=
  ⟨noisy_step_above_quarter hg hq h1,
    noisyRecurrence_strict_decay_below_critical hg.le hc hq⟩

theorem subcriticalOrbit_above_quarter {γ F : ℝ}
    (hg : 0 < γ) (hc : γ < criticalGamma) (hq : 1 / 4 < F) (h1 : F ≤ 1) (n : ℕ) :
    1 / 4 < noisyOrbit γ F n ∧ noisyOrbit γ F n ≤ 1 := by
  induction n with
  | zero => exact ⟨hq, h1⟩
  | succ n ih =>
    rw [noisyOrbit_succ]
    have h := subcritical_step_above_quarter hg hc ih.1 ih.2
    exact ⟨h.1, le_trans h.2.le ih.2⟩

theorem subcriticalOrbit_strictAnti {γ F : ℝ}
    (hg : 0 < γ) (hc : γ < criticalGamma) (hq : 1 / 4 < F) (h1 : F ≤ 1) :
    StrictAnti (noisyOrbit γ F) := by
  apply strictAnti_nat_of_succ_lt
  intro n
  rw [noisyOrbit_succ]
  have h := subcriticalOrbit_above_quarter hg hc hq h1 n
  exact (subcritical_step_above_quarter hg hc h.1 h.2).2

theorem subcritical_stationary_iff {γ : ℝ} (hg : 0 ≤ γ) (hc : γ < criticalGamma) (F : ℝ) :
    (∀ n, noisyOrbit γ F n = F) ↔ F = 1 / 4 := by
  constructor
  · intro h
    apply (noisyRecurrence_subcritical_fixed_iff hg hc F).mp
    simpa [noisyOrbit_succ] using h 1
  · rintro rfl
    exact noisyOrbit_fixed (noisyRecurrence_quarter γ)

/-- Global physical basin in the subcritical regime, including zero quality. -/
theorem subcriticalOrbit_tendsto_quarter {γ F : ℝ}
    (hg : 0 ≤ γ) (hc : γ < criticalGamma) (h0 : 0 ≤ F) (h1 : F ≤ 1) :
    Tendsto (noisyOrbit γ F) atTop (nhds (1 / 4)) := by
  rcases hg.eq_or_lt with he | hg
  · subst γ
    exact zeroQuality_tendsto F
  have hg1 : γ < 1 := lt_trans hc criticalGamma_bounds.2
  rcases lt_trichotomy F (1 / 4) with hq | he | hq
  · have hm := (lowOrbit_strictMono hg hg1 h0 hq).monotone
    have hb : BddAbove (Set.range (noisyOrbit γ F)) :=
      ⟨1 / 4, by rintro _ ⟨n, rfl⟩; exact (lowOrbit_invariant hg hg1 h0 hq n).2.le⟩
    have ht := tendsto_atTop_ciSup hm hb
    have he := (noisyRecurrence_subcritical_fixed_iff hg.le hc _).mp
      (noisyOrbit_limit_is_fixed_point ht)
    rwa [he] at ht
  · subst F
    have he : noisyOrbit γ (1 / 4) = fun _ => (1 / 4 : ℝ) :=
      funext (noisyOrbit_fixed (noisyRecurrence_quarter γ))
    rw [he]
    exact tendsto_const_nhds
  · have hm := (subcriticalOrbit_strictAnti hg hc hq h1).antitone
    have hb : BddBelow (Set.range (noisyOrbit γ F)) :=
      ⟨1 / 4, by
        rintro _ ⟨n, rfl⟩
        exact (subcriticalOrbit_above_quarter hg hc hq h1 n).1.le⟩
    have ht := tendsto_atTop_ciInf hm hb
    have he := (noisyRecurrence_subcritical_fixed_iff hg.le hc _).mp
      (noisyOrbit_limit_is_fixed_point ht)
    rwa [he] at ht

structure QuantumNoisyBBPSSWCriticalSuite : Prop where
  subcritical : ∀ γ F, 0 ≤ γ → γ < criticalGamma → 0 ≤ F → F ≤ 1 →
    Tendsto (noisyOrbit γ F) atTop (nhds (1 / 4))
  critical_mixing : ∀ F, 0 ≤ F → F < criticalFidelity →
    Tendsto (noisyOrbit criticalGamma F) atTop (nhds (1 / 4))
  critical_double : ∀ F, criticalFidelity ≤ F → F ≤ 1 →
    Tendsto (noisyOrbit criticalGamma F) atTop (nhds criticalFidelity)

theorem verification_suite : QuantumNoisyBBPSSWCriticalSuite :=
  ⟨fun _ _ => subcriticalOrbit_tendsto_quarter, fun _ => criticalOrbit_tendsto_quarter,
    fun _ => criticalOrbit_tendsto_double⟩

end QuantumNoisyBBPSSWCritical

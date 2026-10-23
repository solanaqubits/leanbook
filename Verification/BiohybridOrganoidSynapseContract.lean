/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Rational STDP and finite ensemble budget

The rational window is prescribed; its sign is distinct from the clamped change.
An absent event and a zero-lag event are separate inputs with the same local action.
The budget constrains a formal sum of weights, not calibrated metabolism or safety.
No physiological protection, causality mechanism, diffusion or liveness is proved.
-/
namespace BiohybridOrganoidSynapseContract

open scoped BigOperators

@[ext] structure OrganoidSynapseState where
  weight : ℚ
  wMax : ℚ
  hwMax_pos : 0 < wMax
  h_nonneg : 0 ≤ weight
  h_le_max : weight ≤ wMax

structure STDPParameters where
  A_plus : ℚ
  A_minus : ℚ
  tau_plus : ℚ
  tau_minus : ℚ
  h_A_plus_pos : 0 < A_plus
  h_A_minus_pos : 0 < A_minus
  h_tau_plus_pos : 0 < tau_plus
  h_tau_minus_pos : 0 < tau_minus

def stdpWindow (p : STDPParameters) (dt : ℤ) : ℚ :=
  if 0 < dt then p.A_plus * p.tau_plus / (p.tau_plus + |(dt : ℚ)|)
  else if dt < 0 then -(p.A_minus * p.tau_minus / (p.tau_minus + |(dt : ℚ)|))
  else 0

theorem stdp_window_positive (p : STDPParameters) (dt : ℤ) (hdt : 0 < dt) :
    0 < stdpWindow p dt := by
  rw [stdpWindow, if_pos hdt]
  exact div_pos (mul_pos p.h_A_plus_pos p.h_tau_plus_pos)
    (by linarith [p.h_tau_plus_pos, abs_nonneg (dt : ℚ)])

theorem stdp_window_negative (p : STDPParameters) (dt : ℤ) (hdt : dt < 0) :
    stdpWindow p dt < 0 := by
  rw [stdpWindow, if_neg (by omega : ¬ 0 < dt), if_pos hdt]
  exact neg_neg_of_pos (div_pos (mul_pos p.h_A_minus_pos p.h_tau_minus_pos)
    (by linarith [p.h_tau_minus_pos, abs_nonneg (dt : ℚ)]))

@[simp] theorem stdp_window_zero (p : STDPParameters) : stdpWindow p 0 = 0 := by
  simp [stdpWindow]

theorem stdp_asymmetry_sign (p : STDPParameters) (dt : ℤ) :
    (0 < stdpWindow p dt ↔ 0 < dt) ∧
    (stdpWindow p dt < 0 ↔ dt < 0) ∧ (stdpWindow p dt = 0 ↔ dt = 0) := by
  by_cases hp : 0 < dt
  · have hw := stdp_window_positive p dt hp
    have hn : ¬ dt < 0 := by omega
    simp [hp, hn, ne_of_gt hp, hw, not_lt.mpr hw.le, ne_of_gt hw]
  · by_cases hn : dt < 0
    · have hw := stdp_window_negative p dt hn
      simp [hp, hn, ne_of_lt hn, hw, not_lt.mpr hw.le, ne_of_lt hw]
    · have hz : dt = 0 := by omega
      subst dt
      simp

def stdpUpdate (p : STDPParameters) (s : OrganoidSynapseState) (dt : ℤ) :
    OrganoidSynapseState where
  weight := min s.wMax (max 0 (s.weight + stdpWindow p dt))
  wMax := s.wMax
  hwMax_pos := s.hwMax_pos
  h_nonneg := le_min s.hwMax_pos.le (le_max_left _ _)
  h_le_max := min_le_left _ _

theorem weight_bounds_invariant (p : STDPParameters) (s : OrganoidSynapseState) (dt : ℤ) :
    0 ≤ (stdpUpdate p s dt).weight ∧ (stdpUpdate p s dt).weight ≤ s.wMax ∧
      (stdpUpdate p s dt).wMax = s.wMax :=
  ⟨(stdpUpdate p s dt).h_nonneg, (stdpUpdate p s dt).h_le_max, rfl⟩

theorem ltp_monotonicity (p : STDPParameters) (s : OrganoidSynapseState)
    (dt : ℤ) (hdt : 0 < dt) : s.weight ≤ (stdpUpdate p s dt).weight := by
  exact le_min s.h_le_max
    ((le_add_of_nonneg_right (stdp_window_positive p dt hdt).le).trans (le_max_right _ _))

theorem ltd_monotonicity (p : STDPParameters) (s : OrganoidSynapseState)
    (dt : ℤ) (hdt : dt < 0) : (stdpUpdate p s dt).weight ≤ s.weight := by
  exact (min_le_right _ _).trans
    (max_le s.h_nonneg (add_le_of_nonpos_right (stdp_window_negative p dt hdt).le))

theorem stdp_zero_identity (p : STDPParameters) (s : OrganoidSynapseState) :
    stdpUpdate p s 0 = s := by
  ext
  · simp [stdpUpdate, max_eq_right s.h_nonneg, min_eq_right s.h_le_max]
  · rfl

def eventUpdate (p : STDPParameters) (s : OrganoidSynapseState) :
    Option ℤ → OrganoidSynapseState
  | none => s
  | some dt => stdpUpdate p s dt

theorem silence_invariance (p : STDPParameters) (s : OrganoidSynapseState) :
    eventUpdate p s none = s := rfl

theorem zero_event_identity (p : STDPParameters) (s : OrganoidSynapseState) :
    eventUpdate p s (some 0) = s := stdp_zero_identity p s

theorem event_wMax (p : STDPParameters) (s : OrganoidSynapseState) (e : Option ℤ) :
    (eventUpdate p s e).wMax = s.wMax := by cases e <;> rfl

abbrev EnsembleState (K : ℕ) := Fin K → OrganoidSynapseState

def totalWeight {K : ℕ} (s : EnsembleState K) : ℚ := ∑ i, (s i).weight

theorem totalWeight_nonneg {K : ℕ} (s : EnsembleState K) : 0 ≤ totalWeight s :=
  Finset.sum_nonneg (fun i _ => (s i).h_nonneg)

def normalizationFactor {K : ℕ} (B : ℚ) (s : EnsembleState K) : ℚ :=
  if totalWeight s ≤ B then 1 else B / totalWeight s

theorem normalization_factor_bounds {K : ℕ} (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) :
    0 ≤ normalizationFactor B s ∧ normalizationFactor B s ≤ 1 := by
  by_cases h : totalWeight s ≤ B
  · simp [normalizationFactor, h]
  · have ht : 0 < totalWeight s := lt_of_le_of_lt hB (lt_of_not_ge h)
    simp only [normalizationFactor, if_neg h]
    exact ⟨div_nonneg hB ht.le, (div_le_one ht).mpr (le_of_lt (lt_of_not_ge h))⟩

def homeostaticNormalize {K : ℕ} (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) :
    EnsembleState K := fun i => {
  weight := normalizationFactor B s * (s i).weight
  wMax := (s i).wMax
  hwMax_pos := (s i).hwMax_pos
  h_nonneg := mul_nonneg (normalization_factor_bounds B hB s).1 (s i).h_nonneg
  h_le_max := (mul_le_of_le_one_left (s i).h_nonneg
    (normalization_factor_bounds B hB s).2).trans (s i).h_le_max
}

theorem normalized_component_bounds {K : ℕ} (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (i : Fin K) :
    0 ≤ (homeostaticNormalize B hB s i).weight ∧
    (homeostaticNormalize B hB s i).weight ≤ (s i).weight ∧
    (s i).weight ≤ (s i).wMax ∧
    (homeostaticNormalize B hB s i).wMax = (s i).wMax :=
  ⟨(homeostaticNormalize B hB s i).h_nonneg,
    mul_le_of_le_one_left (s i).h_nonneg (normalization_factor_bounds B hB s).2,
    (s i).h_le_max, rfl⟩

theorem total_normalized_factor {K : ℕ} (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) :
    totalWeight (homeostaticNormalize B hB s) = normalizationFactor B s * totalWeight s := by
  simp [totalWeight, homeostaticNormalize, Finset.mul_sum]

theorem total_after_normalize {K : ℕ} (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) :
    totalWeight (homeostaticNormalize B hB s) = min (totalWeight s) B := by
  rw [total_normalized_factor]
  by_cases h : totalWeight s ≤ B
  · simp [normalizationFactor, h]
  · have ht : 0 < totalWeight s := lt_of_le_of_lt hB (lt_of_not_ge h)
    simp [normalizationFactor, h, min_eq_right (le_of_lt (lt_of_not_ge h)),
      div_mul_cancel₀ B (ne_of_gt ht)]

theorem homeostatic_normalization_bound {K : ℕ} (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) : totalWeight (homeostaticNormalize B hB s) ≤ B := by
  rw [total_after_normalize]
  exact min_le_right _ _

theorem normalize_if_within_budget {K : ℕ} (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (hs : totalWeight s ≤ B) : homeostaticNormalize B hB s = s := by
  funext i
  ext
  · simp [homeostaticNormalize, normalizationFactor, hs]
  · rfl

theorem normalization_idempotent {K : ℕ} (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) :
    homeostaticNormalize B hB (homeostaticNormalize B hB s) = homeostaticNormalize B hB s :=
  normalize_if_within_budget B hB _ (homeostatic_normalization_bound B hB s)

/-- Cross-products express preserved proportions without division by a zero component. -/
theorem normalization_cross_ratio {K : ℕ} (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (i j : Fin K) :
    (homeostaticNormalize B hB s i).weight * (s j).weight =
      (homeostaticNormalize B hB s j).weight * (s i).weight := by
  dsimp [homeostaticNormalize]
  ring

def ensembleEventUpdate {K : ℕ} (p : STDPParameters) (s : EnsembleState K)
    (events : Fin K → Option ℤ) : EnsembleState K := fun i => eventUpdate p (s i) (events i)

def ensembleStep {K : ℕ} (p : STDPParameters) (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (events : Fin K → Option ℤ) : EnsembleState K :=
  homeostaticNormalize B hB (ensembleEventUpdate p s events)

theorem ensemble_budget_bound {K : ℕ} (p : STDPParameters) (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (events : Fin K → Option ℤ) :
    totalWeight (ensembleStep p B hB s events) ≤ B :=
  homeostatic_normalization_bound B hB _

theorem ensemble_wMax {K : ℕ} (p : STDPParameters) (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (events : Fin K → Option ℤ) (i : Fin K) :
    (ensembleStep p B hB s events i).wMax = (s i).wMax := by
  exact event_wMax p (s i) (events i)

theorem ensemble_events_silent {K : ℕ} (p : STDPParameters) (s : EnsembleState K)
    (events : Fin K → Option ℤ) (he : ∀ i, events i = none) :
    ensembleEventUpdate p s events = s := by
  funext i
  simp [ensembleEventUpdate, he, eventUpdate]

/-- Local silence alone is insufficient when the initial ensemble is over budget. -/
theorem composite_silence_invariance {K : ℕ} (p : STDPParameters) (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (events : Fin K → Option ℤ) (he : ∀ i, events i = none)
    (hs : totalWeight s ≤ B) : ensembleStep p B hB s events = s := by
  rw [ensembleStep, ensemble_events_silent p s events he, normalize_if_within_budget B hB s hs]

structure BiohybridOrganoidSynapseSuite : Prop where
  local_bounds : ∀ (p : STDPParameters) (s : OrganoidSynapseState) (dt : ℤ),
    0 ≤ (stdpUpdate p s dt).weight ∧ (stdpUpdate p s dt).weight ≤ s.wMax ∧
      (stdpUpdate p s dt).wMax = s.wMax
  potentiation : ∀ (p : STDPParameters) (s : OrganoidSynapseState) (dt : ℤ),
    0 < dt → s.weight ≤ (stdpUpdate p s dt).weight
  depression : ∀ (p : STDPParameters) (s : OrganoidSynapseState) (dt : ℤ),
    dt < 0 → (stdpUpdate p s dt).weight ≤ s.weight
  raw_sign : ∀ (p : STDPParameters) (dt : ℤ),
    (0 < stdpWindow p dt ↔ 0 < dt) ∧ (stdpWindow p dt < 0 ↔ dt < 0) ∧
      (stdpWindow p dt = 0 ↔ dt = 0)
  norm_total : ∀ (K : ℕ) (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K),
    totalWeight (homeostaticNormalize B hB s) = min (totalWeight s) B
  budget : ∀ (K : ℕ) (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K),
    totalWeight (homeostaticNormalize B hB s) ≤ B
  norm_components : ∀ (K : ℕ) (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K) (i : Fin K),
    0 ≤ (homeostaticNormalize B hB s i).weight ∧
    (homeostaticNormalize B hB s i).weight ≤ (s i).weight ∧
    (s i).weight ≤ (s i).wMax ∧
    (homeostaticNormalize B hB s i).wMax = (s i).wMax
  norm_idempotent : ∀ (K : ℕ) (B : ℚ) (hB : 0 ≤ B) (s : EnsembleState K),
    homeostaticNormalize B hB (homeostaticNormalize B hB s) = homeostaticNormalize B hB s
  composite_budget : ∀ (K : ℕ) (p : STDPParameters) (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (events : Fin K → Option ℤ),
    totalWeight (ensembleStep p B hB s events) ≤ B
  local_silence : ∀ (p : STDPParameters) (s : OrganoidSynapseState), eventUpdate p s none = s
  composite_silence : ∀ (K : ℕ) (p : STDPParameters) (B : ℚ) (hB : 0 ≤ B)
    (s : EnsembleState K) (events : Fin K → Option ℤ),
    (∀ i, events i = none) → totalWeight s ≤ B → ensembleStep p B hB s events = s

theorem verification_suite : BiohybridOrganoidSynapseSuite := {
  local_bounds := weight_bounds_invariant
  potentiation := ltp_monotonicity
  depression := ltd_monotonicity
  raw_sign := stdp_asymmetry_sign
  norm_total := fun _ => total_after_normalize
  budget := fun _ => homeostatic_normalization_bound
  norm_components := fun _ => normalized_component_bounds
  norm_idempotent := fun _ => normalization_idempotent
  composite_budget := fun _ => ensemble_budget_bound
  local_silence := silence_invariance
  composite_silence := fun _ => composite_silence_invariance
}

end BiohybridOrganoidSynapseContract

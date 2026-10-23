/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Discrete bounded-count synapse contract

One classified pulse is one event. Weight is the rational occupancy count / N,
not an independent continuous state. Threshold endpoints are active.
No time-to-pulse law, topological invariant, thermal law or material realization
is assumed or established by this finite-state abstraction.
-/
namespace SpintronicSkyrmionSynapseContract

@[ext] structure SkyrmionSynapse (N : ℕ) where
  count : ℕ
  h_le : count ≤ N

def weight {N : ℕ} (s : SkyrmionSynapse N) : ℚ := (s.count : ℚ) / (N : ℚ)

inductive PulseAction where
  | Potentiate
  | Depress
  | Subthreshold
  deriving DecidableEq, Repr

open PulseAction

/-- Inclusive activation at both endpoints, with positive-branch priority. -/
def classifyCurrent (threshold I : ℚ) : PulseAction :=
  if threshold ≤ I then Potentiate else if I ≤ -threshold then Depress else Subthreshold

def step {N : ℕ} (action : PulseAction) (s : SkyrmionSynapse N) : SkyrmionSynapse N :=
  match action with
  | Potentiate => ⟨min N (s.count + 1), Nat.min_le_left _ _⟩
  | Depress => ⟨s.count - 1, (Nat.sub_le _ _).trans s.h_le⟩
  | Subthreshold => s

def stateUpdate {N : ℕ} (threshold I : ℚ) (s : SkyrmionSynapse N) : SkyrmionSynapse N :=
  step (classifyCurrent threshold I) s

def repeatPulse {N : ℕ} (action : PulseAction) : ℕ → SkyrmionSynapse N → SkyrmionSynapse N
  | 0, s => s
  | k + 1, s => step action (repeatPulse action k s)

theorem weight_in_unit_interval {N : ℕ} (hN : 0 < N) (s : SkyrmionSynapse N) :
    0 ≤ weight s ∧ weight s ≤ 1 := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have hc : (0 : ℚ) ≤ s.count := by exact_mod_cast (Nat.zero_le s.count)
  have hb : (s.count : ℚ) ≤ N := by exact_mod_cast s.h_le
  exact ⟨div_nonneg hc hn.le, (div_le_one hn).mpr hb⟩

theorem weight_zero_capacity (s : SkyrmionSynapse 0) : weight s = 0 := by
  simp [weight]

theorem classify_potentiate_iff (threshold I : ℚ) :
    classifyCurrent threshold I = Potentiate ↔ threshold ≤ I := by
  unfold classifyCurrent
  split_ifs <;> simp_all

theorem classify_depress_iff (threshold I : ℚ) (ht : 0 < threshold) :
    classifyCurrent threshold I = Depress ↔ I ≤ -threshold := by
  unfold classifyCurrent
  split_ifs <;> simp_all
  linarith

theorem classify_subthreshold_iff (threshold I : ℚ) :
    classifyCurrent threshold I = Subthreshold ↔ |I| < threshold := by
  rw [abs_lt]
  unfold classifyCurrent
  split_ifs <;> simp_all

theorem classify_positive_endpoint (threshold : ℚ) :
    classifyCurrent threshold threshold = Potentiate := by simp [classifyCurrent]

theorem classify_negative_endpoint (threshold : ℚ) (ht : 0 < threshold) :
    classifyCurrent threshold (-threshold) = Depress :=
  (classify_depress_iff _ _ ht).mpr le_rfl

theorem classify_zero (threshold : ℚ) (ht : 0 < threshold) :
    classifyCurrent threshold 0 = Subthreshold := by
  apply (classify_subthreshold_iff _ _).mpr
  simpa using ht

theorem step_count_bounded {N : ℕ} (a : PulseAction) (s : SkyrmionSynapse N) :
    (step a s).count ≤ N := (step a s).h_le

theorem subthreshold_invariance {N : ℕ} (threshold I : ℚ) (s : SkyrmionSynapse N)
    (hI : |I| < threshold) : stateUpdate threshold I s = s := by
  rw [stateUpdate, (classify_subthreshold_iff _ _).mpr hI]
  rfl

theorem subthreshold_weight_invariance {N : ℕ} (threshold I : ℚ)
    (s : SkyrmionSynapse N) (hI : |I| < threshold) :
    weight (stateUpdate threshold I s) = weight s := by
  rw [subthreshold_invariance threshold I s hI]

theorem zero_current_invariance {N : ℕ} (threshold : ℚ) (ht : 0 < threshold)
    (s : SkyrmionSynapse N) : stateUpdate threshold 0 s = s := by
  rw [stateUpdate, classify_zero threshold ht]
  rfl

theorem stateUpdate_potentiate {N : ℕ} (threshold I : ℚ) (s : SkyrmionSynapse N)
    (hI : threshold ≤ I) : stateUpdate threshold I s = step Potentiate s := by
  rw [stateUpdate, (classify_potentiate_iff _ _).mpr hI]

theorem stateUpdate_depress {N : ℕ} (threshold I : ℚ) (ht : 0 < threshold)
    (s : SkyrmionSynapse N) (hI : I ≤ -threshold) :
    stateUpdate threshold I s = step Depress s := by
  rw [stateUpdate, (classify_depress_iff _ _ ht).mpr hI]

theorem step_count_monotone_potentiate {N : ℕ} (s : SkyrmionSynapse N) :
    s.count ≤ (step Potentiate s).count := by
  dsimp [step]
  exact le_min s.h_le (Nat.le_succ _)

theorem step_count_monotone_depress {N : ℕ} (s : SkyrmionSynapse N) :
    (step Depress s).count ≤ s.count := Nat.sub_le _ _

theorem step_monotonicity_potentiate {N : ℕ} (hN : 0 < N) (s : SkyrmionSynapse N) :
    weight s ≤ weight (step Potentiate s) := by
  apply div_le_div_of_nonneg_right _ ((by exact_mod_cast hN : (0 : ℚ) < N).le)
  exact_mod_cast step_count_monotone_potentiate s

theorem step_monotonicity_depress {N : ℕ} (hN : 0 < N) (s : SkyrmionSynapse N) :
    weight (step Depress s) ≤ weight s := by
  apply div_le_div_of_nonneg_right _ ((by exact_mod_cast hN : (0 : ℚ) < N).le)
  exact_mod_cast step_count_monotone_depress s

theorem repeat_potentiate_count {N : ℕ} (k : ℕ) (s : SkyrmionSynapse N) :
    (repeatPulse Potentiate k s).count = min N (s.count + k) := by
  induction k with
  | zero => simp [repeatPulse, min_eq_right s.h_le]
  | succ k ih =>
    change min N ((repeatPulse Potentiate k s).count + 1) = min N (s.count + (k + 1))
    rw [ih]
    omega

theorem repeat_depress_count {N : ℕ} (k : ℕ) (s : SkyrmionSynapse N) :
    (repeatPulse Depress k s).count = s.count - k := by
  induction k with
  | zero => simp [repeatPulse]
  | succ k ih =>
    change (repeatPulse Depress k s).count - 1 = s.count - (k + 1)
    rw [ih]
    omega

theorem repeat_subthreshold {N : ℕ} (k : ℕ) (s : SkyrmionSynapse N) :
    repeatPulse Subthreshold k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [repeatPulse, step] using ih

theorem repeated_subthreshold_memory {N : ℕ} (threshold I : ℚ) (k : ℕ)
    (s : SkyrmionSynapse N) (hI : |I| < threshold) :
    repeatPulse (classifyCurrent threshold I) k s = s := by
  rw [(classify_subthreshold_iff _ _).mpr hI, repeat_subthreshold]

/-- Exact state-dependent dose, sharper than the uniform bound N. -/
theorem potentiation_saturated_iff {N : ℕ} (k : ℕ) (s : SkyrmionSynapse N) :
    (repeatPulse Potentiate k s).count = N ↔ N - s.count ≤ k := by
  rw [repeat_potentiate_count]
  omega

theorem depression_saturated_iff {N : ℕ} (k : ℕ) (s : SkyrmionSynapse N) :
    (repeatPulse Depress k s).count = 0 ↔ s.count ≤ k := by
  rw [repeat_depress_count]
  omega

theorem saturation_by_dose_potentiate {N : ℕ} (hN : 0 < N) (k : ℕ)
    (s : SkyrmionSynapse N) (hk : N ≤ k) :
    (repeatPulse Potentiate k s).count = N ∧ weight (repeatPulse Potentiate k s) = 1 := by
  have hc : (repeatPulse Potentiate k s).count = N :=
    (potentiation_saturated_iff k s).mpr (by omega)
  refine ⟨hc, ?_⟩
  rw [weight, hc]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hN))

theorem saturation_by_dose_depress {N : ℕ} (k : ℕ)
    (s : SkyrmionSynapse N) (hk : N ≤ k) :
    (repeatPulse Depress k s).count = 0 ∧ weight (repeatPulse Depress k s) = 0 := by
  have hc : (repeatPulse Depress k s).count = 0 :=
    (depression_saturated_iff k s).mpr (s.h_le.trans hk)
  exact ⟨hc, by simp [weight, hc]⟩

/-- Strict current margin only; no stochastic or temperature-dependent pinning law. -/
theorem bounded_disturbance_invariance {N : ℕ} (threshold I δ : ℚ)
    (s : SkyrmionSynapse N) (hmargin : |I| + |δ| < threshold) :
    stateUpdate threshold (I + δ) s = s := by
  apply subthreshold_invariance
  exact (abs_add_le I δ).trans_lt hmargin

structure SpintronicSkyrmionSynapseSuite : Prop where
  weight_bounds : ∀ (N : ℕ), 0 < N → ∀ s : SkyrmionSynapse N,
    0 ≤ weight s ∧ weight s ≤ 1
  inactive_identity : ∀ (N : ℕ) (threshold I : ℚ) (s : SkyrmionSynapse N),
    |I| < threshold → stateUpdate threshold I s = s
  potentiation_monotonicity : ∀ (N : ℕ), 0 < N → ∀ s : SkyrmionSynapse N,
    weight s ≤ weight (step Potentiate s)
  depression_monotonicity : ∀ (N : ℕ), 0 < N → ∀ s : SkyrmionSynapse N,
    weight (step Depress s) ≤ weight s
  potentiation_exact : ∀ (N k : ℕ) (s : SkyrmionSynapse N),
    (repeatPulse Potentiate k s).count = min N (s.count + k)
  depression_exact : ∀ (N k : ℕ) (s : SkyrmionSynapse N),
    (repeatPulse Depress k s).count = s.count - k
  potentiation_saturation : ∀ (N : ℕ), 0 < N → ∀ (k : ℕ) (s : SkyrmionSynapse N),
    N ≤ k → (repeatPulse Potentiate k s).count = N ∧ weight (repeatPulse Potentiate k s) = 1
  depression_saturation : ∀ (N k : ℕ) (s : SkyrmionSynapse N),
    N ≤ k → (repeatPulse Depress k s).count = 0 ∧ weight (repeatPulse Depress k s) = 0
  subthreshold_memory : ∀ (N k : ℕ) (s : SkyrmionSynapse N), repeatPulse Subthreshold k s = s

theorem verification_suite : SpintronicSkyrmionSynapseSuite := {
  weight_bounds := fun _ => weight_in_unit_interval
  inactive_identity := fun _ => subthreshold_invariance
  potentiation_monotonicity := fun _ => step_monotonicity_potentiate
  depression_monotonicity := fun _ => step_monotonicity_depress
  potentiation_exact := fun _ => repeat_potentiate_count
  depression_exact := fun _ => repeat_depress_count
  potentiation_saturation := fun _ => saturation_by_dose_potentiate
  depression_saturation := fun _ => saturation_by_dose_depress
  subthreshold_memory := fun _ => repeat_subthreshold
}

end SpintronicSkyrmionSynapseContract

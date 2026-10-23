/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded rational mean angular momentum

All moments are normalized to units of hbar. Rational transfer is a mean quantity,
not a claim of integer event transfer or an outgoing photon distribution.
The explicit optical remainder closes the prescribed scalar balance at saturation.
No physical injection threshold, QED/STT calibration or device refinement is supplied.
-/
namespace OptospintronicTransducerContract

inductive OpticalPolarization
  | LeftCircular | RightCircular | Linear
  deriving DecidableEq, Repr

structure OpticalPulse where
  photonCount : ℕ
  polarization : OpticalPolarization
  couplingEfficiency : ℚ
  h_eff_nonneg : 0 ≤ couplingEfficiency
  h_eff_le_one : couplingEfficiency ≤ 1

@[ext] structure SpinReservoirState (Smax : ℕ) where
  spinZ : ℚ
  h_lower : -(Smax : ℚ) ≤ spinZ
  h_upper : spinZ ≤ (Smax : ℚ)

def couplingBudget (pulse : OpticalPulse) : ℚ := (pulse.photonCount : ℚ) * pulse.couplingEfficiency

theorem coupling_budget_nonnegative (pulse : OpticalPulse) : 0 ≤ couplingBudget pulse :=
  mul_nonneg (Nat.cast_nonneg _) pulse.h_eff_nonneg

theorem coupling_budget_le_count (pulse : OpticalPulse) :
    couplingBudget pulse ≤ (pulse.photonCount : ℚ) := by
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) pulse.h_eff_le_one

def momentumDelta {Smax : ℕ} (s : SpinReservoirState Smax) (pulse : OpticalPulse) : ℚ :=
  match pulse.polarization with
  | .RightCircular => min (couplingBudget pulse) ((Smax : ℚ) - s.spinZ)
  | .LeftCircular => -min (couplingBudget pulse) (s.spinZ + (Smax : ℚ))
  | .Linear => 0

theorem right_delta_bounds {Smax : ℕ} (s : SpinReservoirState Smax) (pulse : OpticalPulse)
    (hp : pulse.polarization = .RightCircular) :
    0 ≤ momentumDelta s pulse ∧ momentumDelta s pulse ≤ couplingBudget pulse := by
  simp only [momentumDelta, hp]
  exact ⟨le_min (coupling_budget_nonnegative pulse) (sub_nonneg.mpr s.h_upper),
    min_le_left _ _⟩

theorem left_delta_bounds {Smax : ℕ} (s : SpinReservoirState Smax) (pulse : OpticalPulse)
    (hp : pulse.polarization = .LeftCircular) :
    -couplingBudget pulse ≤ momentumDelta s pulse ∧ momentumDelta s pulse ≤ 0 := by
  have h : 0 ≤ min (couplingBudget pulse) (s.spinZ + (Smax : ℚ)) :=
    le_min (coupling_budget_nonnegative pulse) (by linarith [s.h_lower])
  simp only [momentumDelta, hp]
  exact ⟨neg_le_neg (min_le_left _ _), neg_nonpos.mpr h⟩

def transferMomentum {Smax : ℕ} (pulse : OpticalPulse) (s : SpinReservoirState Smax) :
    SpinReservoirState Smax where
  spinZ := s.spinZ + momentumDelta s pulse
  h_lower := by
    cases hp : pulse.polarization with
    | RightCircular => linarith [(right_delta_bounds s pulse hp).1, s.h_lower]
    | LeftCircular =>
      have h := min_le_right (couplingBudget pulse) (s.spinZ + (Smax : ℚ))
      simp only [momentumDelta, hp]
      linarith
    | Linear => simpa [momentumDelta, hp] using s.h_lower
  h_upper := by
    cases hp : pulse.polarization with
    | RightCircular =>
      have h := min_le_right (couplingBudget pulse) ((Smax : ℚ) - s.spinZ)
      simp only [momentumDelta, hp]
      linarith
    | LeftCircular => linarith [(left_delta_bounds s pulse hp).2, s.h_upper]
    | Linear => simpa [momentumDelta, hp] using s.h_upper

theorem actual_transfer_eq_delta {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) : (transferMomentum pulse s).spinZ - s.spinZ =
      momentumDelta s pulse := by simp [transferMomentum]

theorem saturation_bound_invariant {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) : -(Smax : ℚ) ≤ (transferMomentum pulse s).spinZ ∧
      (transferMomentum pulse s).spinZ ≤ (Smax : ℚ) :=
  ⟨(transferMomentum pulse s).h_lower, (transferMomentum pulse s).h_upper⟩

theorem linear_polarization_invariance {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .Linear) : transferMomentum pulse s = s := by
  ext
  simp [transferMomentum, momentumDelta, hp]

theorem right_polarization_monotonicity {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .RightCircular) :
    s.spinZ ≤ (transferMomentum pulse s).spinZ :=
  le_add_of_nonneg_right (right_delta_bounds s pulse hp).1

theorem left_polarization_monotonicity {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .LeftCircular) :
    (transferMomentum pulse s).spinZ ≤ s.spinZ :=
  add_le_of_nonpos_right (left_delta_bounds s pulse hp).2

theorem transferred_momentum_bound {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) : |(transferMomentum pulse s).spinZ - s.spinZ| ≤
      couplingBudget pulse := by
  rw [actual_transfer_eq_delta, abs_le]
  have hb := coupling_budget_nonnegative pulse
  cases hp : pulse.polarization with
  | RightCircular => have h := right_delta_bounds s pulse hp; constructor <;> linarith
  | LeftCircular => have h := left_delta_bounds s pulse hp; constructor <;> linarith
  | Linear => simp [momentumDelta, hp, hb]

theorem zero_budget_identity {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hb : couplingBudget pulse = 0) : transferMomentum pulse s = s := by
  have h := transferred_momentum_bound s pulse
  rw [hb] at h
  have hz := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  ext
  linarith

theorem zero_efficiency_neutrality {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hη : pulse.couplingEfficiency = 0) :
    transferMomentum pulse s = s :=
  zero_budget_identity s pulse (by simp [couplingBudget, hη])

theorem zero_photon_identity {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hn : pulse.photonCount = 0) : transferMomentum pulse s = s :=
  zero_budget_identity s pulse (by simp [couplingBudget, hn])

theorem zero_capacity_identity (s : SpinReservoirState 0) (pulse : OpticalPulse) :
    transferMomentum pulse s = s := by
  have h := saturation_bound_invariant s pulse
  have hs := s.h_lower
  have ht := s.h_upper
  ext
  norm_num at h hs ht
  linarith

theorem right_unsaturated_transfer {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .RightCircular)
    (hh : couplingBudget pulse ≤ (Smax : ℚ) - s.spinZ) :
    (transferMomentum pulse s).spinZ = s.spinZ + couplingBudget pulse := by
  simp [transferMomentum, momentumDelta, hp, min_eq_left hh]

theorem left_unsaturated_transfer {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .LeftCircular)
    (hh : couplingBudget pulse ≤ s.spinZ + (Smax : ℚ)) :
    (transferMomentum pulse s).spinZ = s.spinZ - couplingBudget pulse := by
  simp [transferMomentum, momentumDelta, hp, min_eq_left hh, sub_eq_add_neg]

def polarizationSign : OpticalPolarization → ℚ
  | .LeftCircular => -1
  | .RightCircular => 1
  | .Linear => 0

def signedIncidentMomentum (pulse : OpticalPulse) : ℚ :=
  polarizationSign pulse.polarization * (pulse.photonCount : ℚ)

def requestedMomentum (pulse : OpticalPulse) : ℚ :=
  polarizationSign pulse.polarization * couplingBudget pulse

def uncoupledMomentum (pulse : OpticalPulse) : ℚ :=
  polarizationSign pulse.polarization * ((pulse.photonCount : ℚ) * (1 - pulse.couplingEfficiency))

def saturationRemainder {Smax : ℕ} (s : SpinReservoirState Smax) (pulse : OpticalPulse) : ℚ :=
  requestedMomentum pulse - momentumDelta s pulse

def opticalOutputMomentum {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) : ℚ := uncoupledMomentum pulse + saturationRemainder s pulse

theorem optical_output_eq_incident_sub_delta {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) : opticalOutputMomentum s pulse =
      signedIncidentMomentum pulse - momentumDelta s pulse := by
  unfold opticalOutputMomentum saturationRemainder uncoupledMomentum
    requestedMomentum signedIncidentMomentum couplingBudget
  ring

theorem angular_momentum_conservation {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) : s.spinZ + signedIncidentMomentum pulse =
      (transferMomentum pulse s).spinZ + opticalOutputMomentum s pulse := by
  rw [optical_output_eq_incident_sub_delta]
  simp [transferMomentum]

theorem right_remainder_bounds {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .RightCircular) :
    0 ≤ saturationRemainder s pulse ∧ saturationRemainder s pulse ≤ couplingBudget pulse := by
  have h := right_delta_bounds s pulse hp
  simp only [saturationRemainder, requestedMomentum, hp, polarizationSign, one_mul]
  constructor <;> linarith

theorem left_remainder_bounds {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .LeftCircular) :
    -couplingBudget pulse ≤ saturationRemainder s pulse ∧ saturationRemainder s pulse ≤ 0 := by
  have h := left_delta_bounds s pulse hp
  simp only [saturationRemainder, requestedMomentum, hp, polarizationSign, neg_one_mul]
  constructor <;> linarith

theorem linear_remainder_zero {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .Linear) :
    saturationRemainder s pulse = 0 ∧ opticalOutputMomentum s pulse = 0 := by
  simp [saturationRemainder, requestedMomentum, momentumDelta, opticalOutputMomentum,
    uncoupledMomentum, hp, polarizationSign]

theorem right_output_bounds {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .RightCircular) :
    0 ≤ opticalOutputMomentum s pulse ∧
      opticalOutputMomentum s pulse ≤ (pulse.photonCount : ℚ) := by
  have hd := right_delta_bounds s pulse hp
  have hb := coupling_budget_le_count pulse
  rw [optical_output_eq_incident_sub_delta]
  simp only [signedIncidentMomentum, hp, polarizationSign, one_mul]
  constructor <;> linarith

theorem left_output_bounds {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) (hp : pulse.polarization = .LeftCircular) :
    -(pulse.photonCount : ℚ) ≤ opticalOutputMomentum s pulse ∧
      opticalOutputMomentum s pulse ≤ 0 := by
  have hd := left_delta_bounds s pulse hp
  have hb := coupling_budget_le_count pulse
  rw [optical_output_eq_incident_sub_delta]
  simp only [signedIncidentMomentum, hp, polarizationSign, neg_one_mul]
  constructor <;> linarith

theorem optical_output_magnitude_bound {Smax : ℕ} (s : SpinReservoirState Smax)
    (pulse : OpticalPulse) : |opticalOutputMomentum s pulse| ≤ (pulse.photonCount : ℚ) := by
  rw [abs_le]
  have hn : (0 : ℚ) ≤ pulse.photonCount := Nat.cast_nonneg _
  cases hp : pulse.polarization with
  | RightCircular => have h := right_output_bounds s pulse hp; constructor <;> linarith
  | LeftCircular => have h := left_output_bounds s pulse hp; constructor <;> linarith
  | Linear => rw [(linear_remainder_zero s pulse hp).2]; constructor <;> linarith

structure OptospintronicTransducerSuite : Prop where
  linear_invariance : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    pulse.polarization = .Linear → transferMomentum pulse s = s
  right_monotonicity : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    pulse.polarization = .RightCircular → s.spinZ ≤ (transferMomentum pulse s).spinZ
  left_monotonicity : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    pulse.polarization = .LeftCircular → (transferMomentum pulse s).spinZ ≤ s.spinZ
  transfer_bound : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    |(transferMomentum pulse s).spinZ - s.spinZ| ≤ couplingBudget pulse
  saturation : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    -(Smax : ℚ) ≤ (transferMomentum pulse s).spinZ ∧
      (transferMomentum pulse s).spinZ ≤ (Smax : ℚ)
  zero_efficiency : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    pulse.couplingEfficiency = 0 → transferMomentum pulse s = s
  conservation : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    s.spinZ + signedIncidentMomentum pulse =
      (transferMomentum pulse s).spinZ + opticalOutputMomentum s pulse
  output_bound : ∀ (Smax : ℕ) (s : SpinReservoirState Smax) (pulse : OpticalPulse),
    |opticalOutputMomentum s pulse| ≤ (pulse.photonCount : ℚ)

theorem verification_suite : OptospintronicTransducerSuite := {
  linear_invariance := fun _ => linear_polarization_invariance
  right_monotonicity := fun _ => right_polarization_monotonicity
  left_monotonicity := fun _ => left_polarization_monotonicity
  transfer_bound := fun _ => transferred_momentum_bound
  saturation := fun _ => saturation_bound_invariant
  zero_efficiency := fun _ => zero_efficiency_neutrality
  conservation := fun _ => angular_momentum_conservation
  output_bound := fun _ => optical_output_magnitude_bound
}

end OptospintronicTransducerContract

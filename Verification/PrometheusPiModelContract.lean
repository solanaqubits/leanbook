/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Exact weak-charge factors and a spherical-route latency model

The decimal inputs are exact rational choices in this model. The weak-charge
square is only a scalar factor, not a complete cross section. The chord formula
uses a minor great-circle arc on a sphere; no matter propagation, MSW focusing,
sterile-state encoding, receiver performance or physical feasibility is proved.
All distances are in kilometres and the symbolic speed must use the same units.
-/

namespace PrometheusPiModelContract

noncomputable section

/-- Scalar weak charge, with integer neutron/proton counts and a real mixing input. -/
def weakCharge (neutrons protons : ℕ) (sinSquared : ℝ) : ℝ :=
  neutrons - protons * (1 - 4 * sinSquared)

/-- The chosen exact value, not an uncertainty interval for a measured constant. -/
def mixingInput : ℝ := 231 / 1000

/-- Weak-charge-square factor; omitted kinematics/form factors are not identified. -/
def chargeFactor (neutrons protons : ℕ) : ℝ :=
  weakCharge neutrons protons mixingInput ^ 2

theorem tungsten_charge : weakCharge 110 74 mixingInput = 13047 / 125 := by
  norm_num [weakCharge, mixingInput]

theorem carbon_charge : weakCharge 6 6 mixingInput = 693 / 125 := by
  norm_num [weakCharge, mixingInput]

theorem carbon_factor_pos : 0 < chargeFactor 6 6 := by
  norm_num [chargeFactor, weakCharge, mixingInput]

/-- Exact comparison, avoiding any floating-point rounding. -/
theorem charge_factor_margin :
    chargeFactor 110 74 - 350 * chargeFactor 6 6 = 2137059 / 15625 := by
  norm_num [chargeFactor, weakCharge, mixingInput]

theorem charge_factor_ratio :
    chargeFactor 110 74 / chargeFactor 6 6 = 18913801 / 53361 := by
  norm_num [chargeFactor, weakCharge, mixingInput]

/-- The requested factor exceeds 350 at the specified exact mixing input. -/
theorem charge_factor_advantage : 350 * chargeFactor 6 6 < chargeFactor 110 74 := by
  norm_num [chargeFactor, weakCharge, mixingInput]

/-- Radius of the ideal spherical route model, in kilometres. -/
def earthRadius : ℝ := 6371

/-- Length of the selected minor great-circle surface arc, in kilometres. -/
def surfaceDistance : ℝ := 16000

/-- Exact optical-index choice 1.46; it is not the reciprocal of exactly 0.68. -/
def fiberIndex : ℝ := 73 / 50

/-- Central angle in radians for the selected surface arc. -/
def centralAngle : ℝ := surfaceDistance / earthRadius

/-- Conventional chord formula for the two endpoints of that same arc. -/
def chordDistance : ℝ := 2 * earthRadius * Real.sin (centralAngle / 2)

theorem route_parameters_pos :
    0 < earthRadius ∧ 0 < surfaceDistance ∧ 1 < fiberIndex := by
  norm_num [earthRadius, surfaceDistance, fiberIndex]

/-- The chosen arc is nonzero and shorter than a semicircle. -/
theorem central_angle_domain : 0 < centralAngle ∧ centralAngle < Real.pi := by
  constructor
  · norm_num [centralAngle, surfaceDistance, earthRadius]
  · have hthree : centralAngle < 3 := by
      norm_num [centralAngle, surfaceDistance, earthRadius]
    exact hthree.trans Real.pi_gt_three

theorem half_angle_domain : 0 < centralAngle / 2 ∧ centralAngle / 2 < Real.pi := by
  obtain ⟨hpos, hpi⟩ := central_angle_domain
  constructor <;> linarith

/-- Positive distance, bounded by the sphere's diameter. -/
theorem chord_distance_bounds : 0 < chordDistance ∧ chordDistance ≤ 2 * earthRadius := by
  constructor
  · exact mul_pos (by norm_num [earthRadius])
      (Real.sin_pos_of_pos_of_lt_pi half_angle_domain.1 half_angle_domain.2)
  · have hs := Real.sin_le_one (centralAngle / 2)
    dsimp [chordDistance, earthRadius]
    nlinarith

/-- The diameter already gives a sufficient strict comparison. -/
theorem chord_lt_optical_distance : chordDistance < surfaceDistance * fiberIndex := by
  have hdiameter : 2 * earthRadius < surfaceDistance * fiberIndex := by
    norm_num [earthRadius, surfaceDistance, fiberIndex]
  exact chord_distance_bounds.2.trans_lt hdiameter

/-- Ideal propagation at speed c, excluding emission, detection and processing. -/
def particleTime (c : ℝ) : ℝ := chordDistance / c

/-- Surface propagation at the specified photon speed c / n. -/
def fiberTime (c : ℝ) : ℝ := surfaceDistance / (c / fiberIndex)

theorem fiber_time_eq (c : ℝ) : fiberTime c = (surfaceDistance * fiberIndex) / c := by
  simp only [fiberTime, div_div_eq_mul_div]

theorem propagation_times_pos (c : ℝ) (hc : 0 < c) :
    0 < particleTime c ∧ 0 < fiberTime c := by
  constructor
  · exact div_pos chord_distance_bounds.1 hc
  · exact div_pos route_parameters_pos.2.1
      (div_pos hc (lt_trans (by norm_num) route_parameters_pos.2.2))

/-- Conditional geometric latency comparison for every positive speed c. -/
theorem particle_time_lt_fiber_time (c : ℝ) (hc : 0 < c) :
    particleTime c < fiberTime c := by
  rw [particleTime, fiber_time_eq]
  exact (div_lt_div_iff_of_pos_right hc).2 chord_lt_optical_distance

/-- Only the explicit scalar and ideal geometric properties enter the registry. -/
structure PrometheusPiModelContractSuite : Prop where
  charge_advantage : 350 * chargeFactor 6 6 < chargeFactor 110 74
  charge_ratio : chargeFactor 110 74 / chargeFactor 6 6 = 18913801 / 53361
  angle_domain : 0 < centralAngle ∧ centralAngle < Real.pi
  chord_bounds : 0 < chordDistance ∧ chordDistance ≤ 2 * earthRadius
  latency : ∀ c, 0 < c → particleTime c < fiberTime c

theorem verification_suite : PrometheusPiModelContractSuite :=
  ⟨charge_factor_advantage, charge_factor_ratio, central_angle_domain,
    chord_distance_bounds, particle_time_lt_fiber_time⟩

end
end PrometheusPiModelContract

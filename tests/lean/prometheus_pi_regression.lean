import Verification.PrometheusPiModelContract

open PrometheusPiModelContract

-- Independent exact expected values, not copied conclusions alone.
example : weakCharge 110 74 mixingInput = (104376 : ℝ) / 1000 := by
  norm_num [weakCharge, mixingInput]

example : weakCharge 6 6 mixingInput = (5544 : ℝ) / 1000 := by
  norm_num [weakCharge, mixingInput]

example : 354 < chargeFactor 110 74 / chargeFactor 6 6 := by
  norm_num [chargeFactor, weakCharge, mixingInput]

example : chargeFactor 110 74 / chargeFactor 6 6 < 355 := by
  norm_num [chargeFactor, weakCharge, mixingInput]

-- Counterexample: the claim cannot silently quantify over all mixing inputs.
example : weakCharge 110 74 (1 / 4) ^ 2 < 350 * weakCharge 6 6 (1 / 4) ^ 2 := by
  norm_num [weakCharge]

example : weakCharge 0 0 mixingInput = 0 := by
  norm_num [weakCharge]

-- Exact geometry parameters and independent semicircle bound.
example : centralAngle = (16000 : ℝ) / 6371 := by
  norm_num [centralAngle, surfaceDistance, earthRadius]

example : 0 < centralAngle ∧ centralAngle < Real.pi := central_angle_domain

example : 0 < chordDistance ∧ chordDistance ≤ 12742 := by
  have h := chord_distance_bounds
  norm_num [earthRadius] at h
  exact h

example : surfaceDistance * fiberIndex = 23360 := by
  norm_num [surfaceDistance, fiberIndex]

-- Literal requested speed c/n, checked through the public theorem.
example (c : ℝ) (hc : 0 < c) :
    chordDistance / c < surfaceDistance / (c / fiberIndex) :=
  particle_time_lt_fiber_time c hc

example : particleTime (299792458 / 1000) < fiberTime (299792458 / 1000) :=
  particle_time_lt_fiber_time _ (by norm_num)

example : fiberTime (299792458 / 1000) = (11680000 : ℝ) / 149896229 := by
  norm_num [fiberTime, surfaceDistance, fiberIndex]

-- The two requested fiber baselines differ; equality must not be inferred.
example : (1 : ℝ) / fiberIndex ≠ 68 / 100 := by
  norm_num [fiberIndex]

-- Counterexample to dropping the positive-speed premise: totalized division at 0.
example : particleTime 0 = fiberTime 0 := by
  simp [particleTime, fiberTime]

example : ¬ particleTime 0 < fiberTime 0 := by
  simp [particleTime, fiberTime]

-- Concrete positive-speed witness for the suite's conditional proposition.
example : 0 < particleTime 1 ∧ particleTime 1 < fiberTime 1 :=
  ⟨(propagation_times_pos 1 (by norm_num)).1, verification_suite.latency 1 (by norm_num)⟩

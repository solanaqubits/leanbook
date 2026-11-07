import Verification.QuantumNoisyRepeaterWitness
open QuantumNoisyRepeaterWitness QuantumScheduledNoisyRepeater
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence QuantumBBPSSWDistillation

example : (8022568 / 10000000 : ℝ) ≤ firstLevelVisibility.val ∧
    firstLevelVisibility.val ≤ 8022572 / 10000000 := first_level_visibility_bounds

-- This quantifies over every earlier depth, not only the depth-15 regression.
example (m : ℕ) (hm : m ≤ 15) :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [m] < 4 / 5 :=
  first_level_minimal_depth_16 (by omega)

example : scheduledVisibilityValue witnessGamma witnessInitialVisibility [16] > (4 / 5 : ℝ) :=
  first_level_depth_16_gt_initial

-- A fictitious one-round leap to 0.9 is rejected by exact arithmetic.
example : ¬ (9 / 10 : ℝ) ≤ noisyRecurrence (19 / 20) (73 / 100) := by
  norm_num [noisyRecurrence, recurrence, targetMass, successProbability]

example : noisyRecurrence 0 (1 / 4) ≤ noisyRecurrence 0 1 :=
  noisyRecurrence_mono_of_ge_quarter (by norm_num) (by norm_num) (by norm_num) le_rfl

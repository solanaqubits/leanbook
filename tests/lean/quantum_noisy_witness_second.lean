import Verification.QuantumNoisyRepeaterWitness
open QuantumNoisyRepeaterWitness QuantumScheduledNoisyRepeater

example : (8029727 / 10000000 : ℝ) ≤ secondLevelVisibility.val ∧
    secondLevelVisibility.val ≤ 8029731 / 10000000 := second_level_visibility_bounds

example (m : ℕ) (hm : m ≤ 15) :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, m] <
      firstLevelVisibility.val := second_level_minimal_depth_16 (by omega)

example : scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, 15] <
    (4 / 5 : ℝ) := second_level_depth_15_lt_initial

-- The second target is the improved first output, not the original segment value.
example : firstLevelVisibility.val + (7 / 10000 : ℝ) < secondLevelVisibility.val := by
  linarith [first_level_visibility_bounds.2, second_level_visibility_bounds.1]

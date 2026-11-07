import Verification.QuantumScheduledNoisyRepeater
open QuantumScheduledNoisyRepeater QuantumNoisyBBPSSWTree QuantumNoisyBBPSSW
open QuantumNoisyBBPSSWConvergence QuantumNestedRepeater QuantumHeterogeneousBBPSSW
open QuantumBBPSSWDistillation QuantumCentralDepolarization

private noncomputable def quality : Visibility := ⟨19 / 20, by norm_num, by norm_num⟩

-- Equal resource counts do not make different chronological schedules equivalent.
example : scheduledVisibilityValue quality fourFifthsVisibility [0, 1] = 921728 / 2280805 ∧
    scheduledVisibilityValue quality fourFifthsVisibility [1, 0] = 8340544 / 19404025 ∧
    scheduledRepeaterProbability quality fourFifthsVisibility [0, 1] = 456161 / 781250 ∧
    scheduledRepeaterProbability quality fourFifthsVisibility [1, 0] = 776161 / 1562500 := by
  norm_num [scheduledVisibilityValue, scheduledVisibility, scheduledRepeaterProbability,
    scheduledState, scheduledStepAcc, noisyLevelVisibility, noisyLevelVisibilityValue,
    noisyLevelProbability, noisyTreeProbability, noisyOrbit, quality, fourFifthsVisibility,
    noisyRecurrence, swapFidelity, recurrence, targetMass, successProbability]

example : scheduledRawPairCount [4, 2] = 256 ∧ scheduledRawPairCount [4, 4] = 1024 ∧
    scheduledSegmentCount [4, 2] = 4 ∧ scheduledSegmentCount [4, 4] = 4 := by
  norm_num [scheduledRawPairCount, scheduledSegmentCount]

-- This resource-saving witness is ideal only. Reversing the list loses restoration.
example : (4 / 5 : ℝ) < scheduledVisibilityValue unitVisibility fourFifthsVisibility [4, 2] ∧
    scheduledVisibilityValue unitVisibility fourFifthsVisibility [2, 4] < (4 / 5 : ℝ) := by
  norm_num [scheduledVisibilityValue, scheduledVisibility, scheduledState, scheduledStepAcc,
    noisyLevelVisibility, noisyLevelVisibilityValue, noisyOrbit, unitVisibility,
    fourFifthsVisibility, noisyRecurrence, swapFidelity, recurrence, targetMass,
    successProbability, Function.iterate_succ_apply']

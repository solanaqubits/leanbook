import Verification.QuantumScheduledNoisyRepeater
open QuantumScheduledNoisyRepeater QuantumNoisyBBPSSWTree QuantumNestedRepeater
open QuantumCentralDepolarization QuantumNoisyVisibility

example (γ w : Visibility) : scheduledVisibilityValue γ w [0, 0, 0] = w.val^8 ∧
    scheduledRepeaterProbability γ w [0, 0, 0] = 1 ∧ scheduledRawPairCount [0, 0, 0] = 8 := by
  simpa using scheduled_zero_depths γ w 3

example (w : Visibility) (k m : ℕ) :
    scheduledRepeaterMatrix unitVisibility w (List.replicate k m) =
      nestedRepeaterMatrix m w k := scheduledRepeaterMatrix_ideal_replicate w k m

-- The quality hypothesis is restricted to actual steps, and covers every prefix.
example (γ w : Visibility) (hg : LocalQualityGain γ w [0, 2, 1]) :
    w.val ≤ scheduledVisibilityValue γ w [0, 2] :=
  scheduledVisibility_prefix_sustains_initial_of_local_gain γ w _ hg _ ⟨[1], rfl⟩

example (γ w : Visibility) : 0 < scheduledRepeaterProbability γ w [] ∧
    scheduledVisibilityValue γ w [] = w.val := by
  exact ⟨scheduledRepeaterProbability_pos γ w [], rfl⟩

import Verification.QuantumNoisyRepeaterWitness
open QuantumNoisyRepeaterWitness QuantumScheduledNoisyRepeater
open QuantumNoisyVisibility
open scoped ComplexOrder

example : LocalQualityGain witnessGamma witnessInitialVisibility [16, 16] :=
  witnessSchedule_localQualityGain

example : (4 / 5 : ℝ) < scheduledVisibilityValue witnessGamma witnessInitialVisibility [16] ∧
    (4 / 5 : ℝ) < scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, 16] :=
  witnessSchedule_sustains_initial_quality

example : let D :=
    (scheduledRepeaterProbability witnessGamma witnessInitialVisibility witnessSchedule : ℂ)⁻¹ •
      scheduledRepeaterMatrix witnessGamma witnessInitialVisibility witnessSchedule
    D.PosSemidef ∧ D.trace = 1 := by
  dsimp
  rw [witnessSchedule_conditional]
  exact witnessSchedule_conditional_density

example : scheduledSegmentCount witnessSchedule = 4 ∧
    scheduledRawPairCount witnessSchedule = 17179869184 :=
  ⟨witnessSchedule_resource_count.1, witnessSchedule_resource_count.2.2⟩

-- Four segments and huge raw consumption remain different counters.
example : scheduledRawPairCount witnessSchedule =
    67108864 * scheduledRawPairCount [4, 2] := by
  rw [witnessSchedule_resource_count.2.2]
  norm_num [scheduledRawPairCount]

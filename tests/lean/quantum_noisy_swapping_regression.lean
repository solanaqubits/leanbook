import Verification.QuantumNoisySwapping

open QuantumPauliMatrix QuantumPauliDensityBridge QuantumTwoQubitCPTP
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumNoisyBellInstrument QuantumNoisySwapping
open scoped BigOperators ComplexOrder

private def zeroBps : BoundedBps := ⟨0, by decide, by decide⟩
private def halfBps : BoundedBps := ⟨5000, by decide, by decide⟩
private def fullBps : BoundedBps := ⟨10000, by decide, by decide⟩
private def randomBps : BoundedBps := ⟨7500, by decide, by decide⟩
private def clean : ReadoutModel := ⟨halfBps, zeroBps⟩
private def wrong : ReadoutModel := ⟨halfBps, fullBps⟩
private def randomLabels : ReadoutModel := ⟨fullBps, randomBps⟩
private def lost : ReadoutModel := ⟨zeroBps, zeroBps⟩

private theorem clean_positive : 0 < probability clean.detection := by
  norm_num [probability, clean, halfBps]
private theorem wrong_positive : 0 < probability wrong.detection := clean_positive
private theorem random_positive : 0 < probability randomLabels.detection := by
  norm_num [probability, randomLabels, fullBps]

example : Fintype.card (Option BellMeasurement) = 5 := by decide

-- Complete positivity includes entangled ancillary inputs, for every dimension.
example (d : Nat) (model : ReadoutModel) (o : Option BellMeasurement)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) (hR : R.PosSemidef) :
    (instrumentExtension d model o R).PosSemidef :=
  branch_completely_positive d model o R hR

example (model : ReadoutModel) (ρ : PairState) :
    ∑ o, outcomeProbability model o ρ = 1 := outcomeProbability_total model ρ

example (model : ReadoutModel) (ρ : PairState) (o : Option BellMeasurement) :
    0 ≤ outcomeProbability model o ρ ∧ outcomeProbability model o ρ ≤ 1 :=
  ⟨outcomeProbability_nonnegative model o ρ, outcomeProbability_le_one model o ρ⟩

-- Identical registered label frequencies can hide radically different fidelities.
example (r : BellMeasurement) : reportedMass clean r = reportedMass wrong r :=
  reported_marginals_ignore_corruption clean wrong rfl r

example : acceptedMass clean = (1 / 2 : ℝ) ∧ lostMass clean = (1 / 2 : ℝ) := by
  norm_num [QuantumNoisySwapping.accepted_mass_formula, lost_mass_formula, probability, clean, halfBps]

example : targetOverlap (conditionalState clean clean_positive).matrix = 1 := by
  rw [conditional_fidelity]
  norm_num [probability, clean, zeroBps]

example : targetOverlap (conditionalState wrong wrong_positive).matrix = 0 := by
  rw [conditional_fidelity]
  norm_num [probability, wrong, fullBps]

example : targetOverlap (conditionalState randomLabels random_positive).matrix = (1 / 4 : ℂ) := by
  rw [conditional_fidelity]
  norm_num [probability, randomLabels, randomBps]

-- Rate-weighted overlap is not the postselected fidelity.
example : targetOverlap (acceptedDensity clean) = (1 / 2 : ℂ) := by
  rw [success_weighted_overlap]
  norm_num [probability, clean, zeroBps, halfBps]

example : acceptedMass lost = 0 ∧ acceptedDensity lost = 0 :=
  no_detection_no_success lost rfl
example : ¬ (0 < probability lost.detection) := zero_detection_not_conditionable lost rfl

-- Physical conditionalState cannot be constructed for the zero-mass event.
example (h : 0 < probability lost.detection) : False :=
  zero_detection_not_conditionable lost rfl h

example (model : ReadoutModel) : circuitAcceptedDensity model = acceptedDensity model :=
  circuit_accepted_density_sound model

example (m₁ m₂ : ReadoutModel) (h₁ : 0 < probability m₁.detection)
    (h₂ : 0 < probability m₂.detection) (hc : m₁.corruption = m₂.corruption) :
    (conditionalState m₁ h₁).matrix = (conditionalState m₂ h₂).matrix :=
  detection_does_not_change_conditional m₁ m₂ h₁ h₂ hc

example : targetOverlap (linearChannel fullBps (conditionalState wrong wrong_positive).matrix) =
    (1 / 4 : ℂ) := by
  rw [conditional_after_depolarization]
  norm_num [probability, fullBps]

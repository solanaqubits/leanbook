import Verification.QuantumSelectiveSwapping

open QuantumPauliMatrix QuantumPauliDensityBridge
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumNoisyBellInstrument QuantumGeneralBellReadout QuantumSelectiveSwapping
open scoped BigOperators ComplexOrder

example (model : Readout) (a r : BellMeasurement) :
    0 ≤ model.confusion a r ∧ model.confusion a r ≤ 1 :=
  ⟨model.confusion_nonneg a r, confusion_le_one model a r⟩

-- The general channel need not be doubly stochastic or symmetric.
example : (∑ a, (biasedReadout false).confusion a .phiPlus) = 4 := by
  rw [sum_bell]
  norm_num [biasedReadout]

example (d : Nat) (model : Readout) (o : Option BellMeasurement)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) (hR : R.PosSemidef) :
    (QuantumGeneralBellReadout.instrumentExtension d model o R).PosSemidef :=
  QuantumGeneralBellReadout.branch_completely_positive d model o R hR

example (model : Readout) (ρ : PairState) :
    ∑ o, QuantumGeneralBellReadout.outcomeProbability model o ρ = 1 :=
  QuantumGeneralBellReadout.outcomeProbability_total model ρ

example (old : ReadoutModel) (o : Option BellMeasurement) (M : PairDensity) :
    QuantumGeneralBellReadout.operation (ofSymmetric old) o M =
      QuantumNoisyBellInstrument.operation old o M := symmetric_operation old o M

example (old : ReadoutModel) :
    QuantumSelectiveSwapping.acceptedMass (ofSymmetric old) =
      QuantumNoisySwapping.acceptedMass old := symmetric_mass old

example (old : ReadoutModel) :
    QuantumSelectiveSwapping.acceptedDensity (ofSymmetric old) =
      QuantumNoisySwapping.acceptedDensity old := symmetric_density old

example (model : Readout) :
    QuantumSelectiveSwapping.circuitAcceptedDensity model =
      QuantumSelectiveSwapping.acceptedDensity model := circuit_density_sound model

-- Same average branch accuracy is sufficient for fidelity, not asserted matrix equality.
example (model : Readout) (h : 0 < QuantumSelectiveSwapping.acceptedMass model)
    (hc : ∀ a, model.confusion a a = (3 / 4 : ℝ)) :
    correctMass model / QuantumSelectiveSwapping.acceptedMass model = 3 / 4 :=
  constant_accuracy_fidelity model h _ hc

-- Symmetric confusion retains its state even under outcome-dependent detection.
example (model : Readout) (old : ReadoutModel)
    (hc : model.confusion = QuantumNoisyBellInstrument.confusion old)
    (h : 0 < QuantumSelectiveSwapping.acceptedMass model) :
    (QuantumSelectiveSwapping.conditionalState model h).matrix =
      QuantumNoisySwapping.labelMixture old :=
  symmetric_confusion_loss_invariant model old hc h

example : QuantumSelectiveSwapping.acceptedMass (biasedReadout true) = (1 / 4 : ℝ) :=
  biased_mass true

example : targetOverlap
    (QuantumSelectiveSwapping.conditionalState
      (biasedReadout false) (biased_positive false)).matrix =
    (1 / 4 : ℂ) := selection_bias_counterexample.1

example : targetOverlap
    (QuantumSelectiveSwapping.conditionalState
      (biasedReadout true) (biased_positive true)).matrix = 1 :=
  selection_bias_counterexample.2.1

example : correctMass (biasedReadout false) = correctMass (biasedReadout true) :=
  selection_bias_counterexample.2.2.2.symm

private noncomputable def blind : Readout :=
  { biasedReadout false with
    detection := fun _ => 0
    detection_nonneg := fun _ => le_refl 0
    detection_le_one := fun _ => by norm_num }

example : QuantumSelectiveSwapping.acceptedMass blind = 0 :=
  (zero_mass_iff blind).mpr (fun _ => rfl)

example : QuantumSelectiveSwapping.acceptedDensity blind = 0 :=
  zero_mass_zero_density blind ((zero_mass_iff blind).mpr (fun _ => rfl))

example (h : 0 < QuantumSelectiveSwapping.acceptedMass blind) : False := by
  have hz := (zero_mass_iff blind).mpr (fun _ => rfl)
  linarith

-- A zero overall mass forces every physical branch's detection probability to zero.
example (model : Readout) (hz : QuantumSelectiveSwapping.acceptedMass model = 0)
    (a : BellMeasurement) : model.detection a = 0 := (zero_mass_iff model).mp hz a

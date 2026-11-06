import Verification.QuantumCorrelatedPostNoise
import Verification.QuantumCorrelatedProbabilityWitness

noncomputable section
open QuantumGateNoiseComposition QuantumCorrelatedMemoryBSM QuantumOrderedNoiseComposition
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumRectangularSwapping QuantumStateAvailabilityContract QuantumGeneralBellReadout
open QuantumOutcomeInstrument QuantumPersistentEnvironment QuantumCentralDepolarization
open QuantumCorrelatedMemoryWitness QuantumCorrelatedProbabilityWitness QuantumBellDiagonalSwapping
open QuantumCorrelatedPostNoise
open scoped BigOperators Matrix Kronecker ComplexOrder

-- Arbitrary post noise cannot remove the GHZ correlation-dependent probability gap.
example (post : BellMeasurement → CPTP PairIndex (Fin 2)) :
    (noisyJointOutcome witnessStages post perfectReadout (some .phiPlus) probWitnessPlus).trace =
        (1/2 : ℂ) ∧
      (noisyJointOutcome witnessStages post perfectReadout (some .phiPlus) probWitnessMinus).trace =
        0 := by
  simpa only [QuantumCorrelatedPostNoise.noisy_outcome_trace] using
    probWitness_phiPlus_branch_trace_shift

-- Nor can it turn a physically impossible PSD branch into a nonzero state.
example (post : BellMeasurement → CPTP PairIndex (Fin 2)) :
    noisyJointOutcome witnessStages post perfectReadout (some .phiPlus) probWitnessMinus = 0 :=
  (noisy_zero_iff_original _ _ _ _ _ probWitnessMinus_valid.1).mpr probWitness_phiPlus_minus_zero

def noVisibility : Visibility := ⟨0, by norm_num, by norm_num⟩

-- In contrast, post noise CAN erase a matrix distinction when the traces already agree.
example (r : BellMeasurement) :
    noisyJointOutcome witnessStages (fun _ => depolarizing noVisibility)
        perfectReadout (some r) witnessPlus =
      noisyJointOutcome witnessStages (fun _ => depolarizing noVisibility)
        perfectReadout (some r) witnessMinus := by
  change (depolarizing noVisibility).map (reducedJointOutcome _ _ _ _) =
    (depolarizing noVisibility).map (reducedJointOutcome _ _ _ _)
  rw [depolarizing_map, depolarizing_map]
  have h := witness_same_branch_trace_but_diff_branch_matrix r
  simp only [noVisibility, Complex.ofReal_zero, zero_smul, zero_add]
  rw [h.1, h.2.1]

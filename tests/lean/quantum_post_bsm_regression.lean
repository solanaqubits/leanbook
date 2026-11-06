import Verification.QuantumPostBSMEnvironment
import Verification.QuantumCorrelatedProbabilityWitness

noncomputable section
open QuantumPostBSMEnvironment QuantumDecoupledEnvironment QuantumCorrelatedMemoryBSM
open QuantumCorrelatedProbabilityWitness QuantumCorrelatedMemoryWitness
open QuantumOrderedNoiseComposition QuantumStateAvailabilityContract QuantumGeneralBellReadout
open QuantumOutcomeInstrument QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumEntanglementSwappingPurificationContract
open scoped Matrix Kronecker ComplexOrder

-- No PSD, product-input, perfect-readout or ideal-analyzer restriction.
example (ss : List (Stage (FourIndex × Fin 2))) (model : Readout) (o : Outcome)
    (N : JointFourDensity (Fin 2)) :
    reducedJointOutcome (ss ++ [postStage]) model o N = reducedJointOutcome ss model o N :=
  post_interaction_outcome_invariant ss model o N

example : ¬ ∃ (A : FourDensity) (B : Matrix (Fin 2) (Fin 2) ℂ),
    postBSMCnotBE.matrix = A ⊗ₖ B := postBSMCnotBE_not_kronecker_product

example : probeState.PosSemidef ∧ probeState.trace = 1 ∧
    postBSMCnotBE.channel.map probeState ≠ probeState :=
  ⟨probeState_positive, probeState_trace_one, post_changes_joint_probe⟩

example : ¬ ∃ (u : FourIndex → ℂ) (v : Fin 2 → ℂ),
    ∀ i q, coupledKet (i,q) = u i * v q := coupledKet_not_product

-- Both correlated GHZ witnesses become indistinguishable for this configuration.
example (model : Readout) (o : Outcome) :
    reducedJointOutcome postCoupledBSMStages model o probWitnessPlus =
      reducedJointOutcome postCoupledBSMStages model o probWitnessMinus := by
  rw [postBSMCnotBE_preserves_all_reducedJointOutcomes,
    postBSMCnotBE_preserves_all_reducedJointOutcomes, probWitness_same_system_marginal]

-- The Bell witnesses of v4.21 likewise share the reduced outcome here.
example (model : Readout) (o : Outcome) :
    reducedJointOutcome postCoupledBSMStages model o witnessPlus =
      reducedJointOutcome postCoupledBSMStages model o witnessMinus := by
  rw [postBSMCnotBE_preserves_all_reducedJointOutcomes,
    postBSMCnotBE_preserves_all_reducedJointOutcomes, witness_same_system_marginal]

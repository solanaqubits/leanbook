import Verification.QuantumDecoupledEnvironment
import Verification.QuantumCorrelatedProbabilityWitness

noncomputable section
open QuantumDecoupledEnvironment QuantumCorrelatedProbabilityWitness
open QuantumCorrelatedMemoryBSM QuantumPersistentEnvironment QuantumOrderedNoiseComposition
open QuantumGateNoiseComposition QuantumMultiStageBSM QuantumBellDiagonalInputs
open QuantumStateAvailabilityContract QuantumGeneralBellReadout QuantumOutcomeInstrument
open scoped BigOperators ComplexOrder Matrix

-- Arbitrary correlated matrices, arbitrary readout, and all five outcomes.
example (ss : List (Stage FourIndex)) (model : Readout) (o : Outcome)
    (N : JointFourDensity (Fin 3)) :
    reducedJointOutcome (extendStages ss) model o N =
      QuantumMultiStageBSM.outcome ss model o (traceEnvironment N) :=
  extendStages_outcome_depends_only_on_system_marginal ss model o N

-- The concrete correlation witness cannot distinguish uncoupled system dynamics.
example (ss : List (Stage FourIndex)) (model : Readout) (o : Outcome) :
    reducedJointOutcome (extendStages ss) model o probWitnessPlus =
      reducedJointOutcome (extendStages ss) model o probWitnessMinus :=
  extendStages_same_system_marginal_eq_output ss model o _ _ probWitness_same_system_marginal

-- A reset environment channel is trace preserving but is NOT required to be unital.
example (S : CPTP (Fin 2) (Fin 3)) (N : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    traceEnvironment ((tensorCPTP S (reset 0)).map N) = S.map (traceEnvironment N) :=
  traceEnvironment_tensorCPTP S (reset 0) N

example : ((reset 0).map (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 2 := by
  norm_num [CPTP.map, reset, resetOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

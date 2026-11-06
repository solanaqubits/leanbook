import Verification.QuantumTensorStageEnvironment
import Verification.QuantumCorrelatedProbabilityWitness

noncomputable section
open QuantumTensorStageEnvironment QuantumDecoupledEnvironment QuantumNoiseTransport
open QuantumCorrelatedProbabilityWitness QuantumCorrelatedMemoryBSM QuantumPersistentEnvironment
open QuantumGateNoiseComposition QuantumOrderedNoiseComposition QuantumMultiStageBSM
open QuantumStateAvailabilityContract QuantumGeneralBellReadout QuantumOutcomeInstrument
open QuantumBellDiagonalInputs
open scoped Matrix

-- Different label types on different environment steps, including nonunital reset.
def resetEnvStage : Stage (Fin 2) :=
  ⟨Fin 2, inferInstance, identityGate _, reset 0⟩

def quietEnvStage (U : UnitaryGate (Fin 2)) : Stage (Fin 2) :=
  ⟨Unit, inferInstance, U, identityChannel _⟩

example (s t : Stage FourIndex) (U : UnitaryGate (Fin 2)) (model : Readout) (o : Outcome) :
    reducedJointOutcome (tensorStages [(s,resetEnvStage),(t,quietEnvStage U)])
        model o probWitnessPlus =
      QuantumMultiStageBSM.outcome [s,t] model o (traceEnvironment probWitnessPlus) :=
  tensorStages_outcome_marginal_reduction _ model o _

-- Identity specialization identifies actions despite labels versus labels times Unit.
example (ss : List (Stage FourIndex)) (N : JointFourDensity (Fin 2)) :
    run (ss.map fun s => tensorStage s (identityGate (Fin 2)) (identityChannel (Fin 2))) N =
      run (extendStages ss) N := tensorStages_identity_run ss N

example : ((reset 0).map (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 2 := by
  norm_num [CPTP.map, reset, resetOperator, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]

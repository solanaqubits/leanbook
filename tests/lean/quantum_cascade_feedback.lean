import Verification.QuantumCascadedSwapping
import Verification.QuantumCorrelatedProbabilityWitness

noncomputable section
open QuantumCascadedSwapping QuantumCorrelatedMemoryBSM QuantumCorrelatedPostNoise
open QuantumCorrelatedMemoryWitness QuantumCorrelatedProbabilityWitness
open QuantumMixedEnvironment QuantumGateNoiseComposition QuantumGeneralBellReadout
open QuantumBellDiagonalSwapping QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumOutcomeInstrument
open scoped BigOperators ComplexOrder Matrix Kronecker

-- Delivered phiPlus switches off detection in round two; other messages do not.
def lossReadout : Readout :=
  { perfectReadout with
    detection := fun _ => 0
    detection_nonneg := fun _ => le_rfl
    detection_le_one := fun _ => by norm_num }

def testRound (model : Readout) : Round (Fin 2) Unit where
  stages := witnessStages
  analyzer := witness_ideal
  post := fun _ => identityChannel PairIndex
  readout := model

def feedbackCascade (τ : EnvironmentState PairIndex) (σ : EnvironmentState (Fin 2)) :
    Cascade (Fin 2) (Fin 2) Unit Unit where
  first := testRound perfectReadout
  second := fun r => testRound (if r = .phiPlus then lossReadout else perfectReadout)
  freshPair := fun _ => τ
  freshMemory := fun _ => σ

lemma loss_message_zero (r : BellMeasurement) (N : JointFourDensity (Fin 2)) :
    ((testRound lossReadout).branch (some r)).map N = 0 := by
  rw [Round.branch_map]
  simp only [testRound, identity_post_refinement, reduced_outcome_some]
  simp [reducedJointMicro_kraus, QuantumSwappingInstrument.weight, lossReadout]

-- A zero physical first branch has zero continuations for every possible second message/reject.
example (τ : EnvironmentState PairIndex) (σ : EnvironmentState (Fin 2)) (o : Outcome) :
    (cascadeBranch (feedbackCascade τ σ) .phiPlus o).map probWitnessMinus = 0 := by
  apply zero_first_branch_gives_zero_continuation _ _ _ _ probWitnessMinus_valid.1
  rw [Round.branch_map]
  simp only [feedbackCascade, testRound, identity_post_refinement]
  rw [probWitness_phiPlus_branch_trace_shift.2]
  rfl

-- The first probability is 1/2; feedback routes it entirely to SECOND rejection.
example (τ : EnvironmentState PairIndex) (σ : EnvironmentState (Fin 2)) :
    ((terminalBranch (feedbackCascade τ σ) (some (.phiPlus, none))).map
      probWitnessPlus).trace = (1/2 : ℂ) := by
  have hz (r : BellMeasurement) :
      (cascadeBranch (feedbackCascade τ σ) .phiPlus (some r)).map probWitnessPlus = 0 := by
    unfold cascadeBranch continuation
    rw [KrausBranch.comp_map, KrausBranch.comp_map]
    change ((testRound lossReadout).branch (some r)).map _ = 0
    exact loss_message_zero r _
  have hs (C : Cascade (Fin 2) (Fin 2) Unit Unit) (r : BellMeasurement)
      (N : JointFourDensity (Fin 2)) :
      (∑ o : Outcome, ((cascadeBranch C r o).map N).trace) =
        ((C.first.branch (some r)).map N).trace := by
    simp only [cascadeBranch, KrausBranch.comp_map, continuation_total_trace]
  have h := hs (feedbackCascade τ σ) .phiPlus probWitnessPlus
  simp only [Fintype.sum_option, hz, Matrix.trace_zero, Finset.sum_const_zero, add_zero] at h
  change ((cascadeBranch (feedbackCascade τ σ) .phiPlus none).map probWitnessPlus).trace = _
  rw [h, Round.branch_map]
  simp only [feedbackCascade, testRound, identity_post_refinement]
  exact probWitness_phiPlus_branch_trace_shift.1

-- All 21 probabilities still add to one, including early rejection separately.
example (τ : EnvironmentState PairIndex) (σ : EnvironmentState (Fin 2)) :
    (∑ o : TerminalOutcome,
      ((terminalBranch (feedbackCascade τ σ) o).map probWitnessPlus).trace.re) = 1 :=
  terminal_probabilities_sum_one _ _ probWitnessPlus_valid.2

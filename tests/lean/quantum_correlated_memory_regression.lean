import Verification.QuantumCorrelatedMemoryWitness

noncomputable section
open QuantumCorrelatedMemoryBSM QuantumCorrelatedMemoryWitness
open QuantumBellDiagonalInputs QuantumRectangularSwapping QuantumStateAvailabilityContract
open QuantumEntanglementSwappingPurificationContract QuantumGeneralBellReadout
open QuantumOutcomeInstrument QuantumOrderedNoiseComposition QuantumPersistentEnvironment
open QuantumMixedEnvironment
open scoped BigOperators Kronecker ComplexOrder

-- CP is asserted on every finite ancilla and every joint input, without a product hypothesis.
example (ss : List (Stage (FourIndex × Fin 2))) (model : Readout) (o : Outcome) :
    IsCPMap (reducedJointOutcome ss model o) := reducedJointOutcome_cp ss model o

-- The product and mixture limits still use the existing v4.20 instrument.
example (ss : List (Stage (FourIndex × Fin 2))) (model : Readout) (o : Outcome)
    (M : Fin 2 → FourDensity) (σ : Fin 2 → EnvironmentState (Fin 2)) :
    reducedJointOutcome ss model o (∑ i, (1/2 : ℂ) • (M i ⊗ₖ (σ i).matrix)) =
      ∑ i, (1/2 : ℂ) • QuantumMixedMemoryBSM.outcome ss (σ i) model o (M i) :=
  reducedJointOutcome_sum_products ss model o (fun _ => 1/2) M σ

-- The chronological stage list starts with an identity ideal gate, then the controlled noise.
example (N : JointFourDensity (Fin 2)) :
    (effective witnessStages).map N = coupling.channel.map N := witness_effective N

-- Neither the system marginal nor the environment marginal identifies the output.
example : traceEnvironment witnessPlus = traceEnvironment witnessMinus ∧
    traceSystem witnessPlus = traceSystem witnessMinus ∧
    accepted witnessPlus ≠ accepted witnessMinus :=
  ⟨witness_same_system_marginal, witness_same_environment_marginal,
    witness_accepted_outputs_distinct⟩

example (r : BellMeasurement) :
    (reducedJointOutcome witnessStages QuantumBellDiagonalSwapping.perfectReadout
      (some r) witnessPlus).trace = (1/4 : ℂ) ∧
    (reducedJointOutcome witnessStages QuantumBellDiagonalSwapping.perfectReadout
      (some r) witnessMinus).trace = (1/4 : ℂ) :=
  ⟨(witness_same_branch_trace_but_diff_branch_matrix r).1,
    (witness_same_branch_trace_but_diff_branch_matrix r).2.1⟩

example : targetOverlap (accepted witnessPlus) = 1 ∧
    targetOverlap (accepted witnessMinus) = 0 := accepted_fidelity_gap

-- No choice of function, even nonlinear, repairs the lost correlation information.
example (r : BellMeasurement) :
    ¬ ∃ f : FourDensity → PairDensity, ∀ N : JointFourDensity (Fin 2),
      N.PosSemidef → N.trace = 1 → f (traceEnvironment N) =
        reducedJointOutcome witnessStages QuantumBellDiagonalSwapping.perfectReadout (some r) N :=
  no_marginal_only_map_for_witness_config r

-- Null-branch behavior applies to these correlated inputs as well.
example (ss : List (Stage (FourIndex × Fin 2))) (model : Readout) (o : Outcome)
    (h : (reducedJointOutcome ss model o witnessPlus).trace.re = 0) :
    reducedJointOutcome ss model o witnessPlus = 0 :=
  (reducedJointOutcome_zero_iff ss model o witnessPlus
    witnessPlus_posSemidef_and_trace_one.1).mp h

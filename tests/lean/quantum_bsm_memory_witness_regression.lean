import Verification.QuantumBSMMemoryWitness

noncomputable section
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout QuantumNoisyBellInstrument
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization
open QuantumNoiseTransport QuantumOrderedNoiseComposition QuantumPersistentEnvironment
open QuantumEnvironmentExtension QuantumBinaryMemoryCoupling QuantumBSMMemoryWitness
open scoped BigOperators ComplexOrder Matrix

-- Generic flag coupling is unitary and its discarded memory implements dephasing.
example (f : Fin 3 → Bool) : couplingMatrix f * couplingMatrix f = 1 := coupling_squared f
example (f : Fin 3 → Bool) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (reduced (coupling f).channel false).map M = dephase f M := reduced_coupling f M
example (M : Matrix (Fin 3) (Fin 3) ℂ) : dephase (fun _ => true) M = M := by
  ext i j : 2
  simp [dephase]
example (f : Fin 3 → Bool) (M : Matrix (Fin 3) (Fin 3) ℂ) (hM : M.PosSemidef) :
    (dephase f M).PosSemidef ∧ (dephase f M).trace = M.trace := by
  rw [← reduced_coupling]
  exact ⟨(reduced (coupling f).channel false).positive M hM,
    (reduced (coupling f).channel false).trace M⟩

-- The precise joint circuit, not a guessed effective scalar noise parameter.
example (M : FourDensity) : (QuantumMemoryBSM.effectivePre echoStages false).map M = M :=
  effective_echo M
example (model : Readout) (o : Outcome) (M : FourDensity) :
    retainedOutcome model o M = outcomeMap model o M := retained_outcome model o M
example (model : Readout) (o : Outcome) (M : FourDensity) :
    resetOutcome model o M = outcomeMap model o (dephase outerFlag M) := reset_outcome model o M

-- The input and both aggregate outputs are legitimate normalized states.
example : input.PosSemidef ∧ input.trace = 1 := input_valid
example : retainedOutput.PosSemidef ∧ resetOutput.PosSemidef := outputs_positive
example : retainedOutput.trace = 1 ∧ resetOutput.trace = 1 := outputs_normalized
example : retainedOutcome QuantumBellDiagonalSwapping.perfectReadout none input = 0 ∧
    resetOutcome QuantumBellDiagonalSwapping.perfectReadout none input = 0 := rejection_absent

-- All four reports agree in probability, but disagree in their output density.
example (r : BellMeasurement) :
    (retainedOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input).trace.re = 1/4 ∧
    (resetOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input).trace.re = 1/4 :=
  same_report_probabilities r
example : targetOverlap retainedOutput = 1 ∧ targetOverlap resetOutput = (1/2 : ℂ) :=
  output_fidelity_gap
example : retainedOutput (0,0) (1,1) = (1/2 : ℂ) ∧ resetOutput (0,0) (1,1) = 0 :=
  output_coherence_gap
example : retainedOutput ≠ resetOutput := outputs_distinct

-- Old circuit-level CP proof remains valid on the explicit entangling joint channels.
example (model : Readout) (o : Outcome)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (hR : R.PosSemidef) :
    (liftMap 2 (QuantumMemoryBSM.outcome echoStages false model o) R).PosSemidef := by
  have h : (ideal echoStages).matrix = extend (embedBC analysisUnitary) :=
    QuantumMemoryBSM.memory_ideal _ _
  exact QuantumMemoryBSM.outcome_cp echoStages false h model o 2 R hR

-- Postselection is safe because every message here has strictly positive probability.
example (r : BellMeasurement) :
    targetOverlap (QuantumNullConditioning.normalizeOrZero
      (resetOutcome QuantumBellDiagonalSwapping.perfectReadout (some r) input)) = (1/2 : ℂ) := by
  rw [QuantumNullConditioning.normalizeOrZero, if_pos (by
    rw [(same_report_probabilities r).2]; norm_num)]
  rw [(same_report_probabilities r).2, reset_branch]
  simp only [smul_smul]
  norm_num
  change targetOverlap mixedOuter = (1/2 : ℂ)
  rw [← reset_output]
  exact output_fidelity_gap.2

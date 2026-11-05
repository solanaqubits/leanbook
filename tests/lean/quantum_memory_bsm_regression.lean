import Verification.QuantumMemoryBSM

noncomputable section
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumPersistentEnvironment QuantumEnvironmentExtension
open QuantumMemoryBSM
open scoped BigOperators ComplexOrder Matrix

-- Rectangular branch elimination works independently of BSM and normalization.
example (K : Fin 2 → Matrix (Fin 3 × Fin 2) (Fin 4 × Fin 2) ℂ)
    (M : Matrix (Fin 4) (Fin 4) ℂ) :
    traceEnvironment (∑ k, K k * prepare (1 : Fin 2) M * (K k).conjTranspose) =
      ∑ kr : Fin 2 × Fin 2,
        (select (n := Fin 3) kr.2 * K kr.1 * insert (n := Fin 4) (1 : Fin 2)) * M *
        (select (n := Fin 3) kr.2 * K kr.1 * insert (n := Fin 4) (1 : Fin 2)).conjTranspose :=
  branch_partial_trace K 1 M

variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable (E : CPTP (FourIndex × Fin 2) κ) (F : CPTP (FourIndex × Fin 2) ι)

-- Heterogeneous noise indices and final environment trace index remain separate.
example : Fintype.card (Paths (memoryStages E F) × Fin 2) =
    Fintype.card κ * Fintype.card ι * 2 := by
  change Fintype.card ((κ × (ι × Unit)) × Fin 2) = _
  simp

-- The joint chronology has no inserted partial trace or fresh environment.
example (M : Matrix (FourIndex × Fin 2) (FourIndex × Fin 2) ℂ) :
    run (memoryStages E F) M =
      F.map (extend (embedBC hadamardControl) *
        E.map (extend (embedBC cnot) * M * (extend (embedBC cnot)).conjTranspose) *
        (extend (embedBC hadamardControl)).conjTranspose) := memory_run E F M

example (model : Readout) (m r : BellMeasurement) (M : FourDensity) :
    traceEnvironment (jointMicro (memoryStages E F) model m r (prepare (1 : Fin 2) M)) =
      micro (memoryStages E F) (1 : Fin 2) model m r M := micro_partial_trace _ _ _ _ _ _

example (model : Readout) (o : Outcome) (M : FourDensity) :
    traceEnvironment (jointOutcome (memoryStages E F) model o (prepare (1 : Fin 2) M)) =
      outcome (memoryStages E F) (1 : Fin 2) model o M := outcome_partial_trace _ _ _ _ _

example (model : Readout) (M : FourDensity) :
    outcome (memoryStages E F) (0 : Fin 2) model none M =
      lostMap model ((effectivePre (memoryStages E F) (0 : Fin 2)).map M) :=
  memory_outcome_bridge E F 0 model none M

-- CP for an ancillary entangled block; no separability premise.
example (model : Readout) (o : Outcome)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (hR : R.PosSemidef) :
    (liftMap 2 (outcome (memoryStages E F) (0 : Fin 2) model o) R).PosSemidef :=
  outcome_cp _ 0 (memory_ideal E F) model o 2 R hR

example (model : Readout) (ρ : FourState) :
    (∑ o : Outcome, outcome (memoryStages E F) (0 : Fin 2) model o ρ.matrix).trace = 1 := by
  rw [total_trace _ 0 (memory_ideal E F), ρ.trace_one]

example (model : Readout) (ρ : FourState) :
    (∑ o : Outcome, jointOutcome (memoryStages E F) model o
      (prepare (0 : Fin 2) ρ.matrix)).trace = 1 := by
  rw [joint_total_trace _ 0 (memory_ideal E F), ρ.trace_one]

example (model : Readout) (o : Outcome) (ρ : FourState) :
    (outcome (memoryStages E F) (0 : Fin 2) model o ρ.matrix).trace.re = 0 ↔
      outcome (memoryStages E F) (0 : Fin 2) model o ρ.matrix = 0 :=
  outcome_zero_iff _ 0 (memory_ideal E F) _ _ _ ρ.positive

-- The ideal limit preserves the earlier GHZ forbidden branch, including its entire matrix.
example : outcome (memoryStages (identityChannel (FourIndex × Fin 2))
    (identityChannel (FourIndex × Fin 2))) (0 : Fin 2)
      QuantumBellDiagonalSwapping.perfectReadout (some .psiPlus) ghzState.matrix = 0 := by
  rw [memory_no_noise]
  exact QuantumNullConditioning.ghz_ideal_report_null.1

-- Environment size is generic; one-dimensional idle environment changes no outcome.
example (model : Readout) (o : Outcome) (M : FourDensity) :
    outcome (memoryStages (identityChannel (FourIndex × Unit))
      (identityChannel (FourIndex × Unit))) () model o M = outcomeMap model o M :=
  memory_no_noise () model o M

-- Arbitrary message-dependent post noise remains compatible with the old accepted channel.
example {α : Type} [Fintype α] (post : BellMeasurement → CPTP PairIndex α)
    (model : Readout) (M : FourDensity) :
    accepted (memoryStages E F) (0 : Fin 2) post model M =
      QuantumNoisyVisibility.noisyAccepted (effectivePre (memoryStages E F) (0 : Fin 2))
        post model M := accepted_bridge _ 0 (memory_ideal E F) post model M

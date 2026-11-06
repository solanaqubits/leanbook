import Verification.QuantumCorrelatedPostNoise

noncomputable section
open QuantumGateNoiseComposition QuantumCorrelatedMemoryBSM QuantumOrderedNoiseComposition
open QuantumBellDiagonalInputs QuantumEntanglementSwappingPurificationContract
open QuantumRectangularSwapping QuantumStateAvailabilityContract QuantumGeneralBellReadout
open QuantumOutcomeInstrument QuantumPersistentEnvironment QuantumMixedEnvironment
open QuantumEnvironmentExtension QuantumCentralDepolarization QuantumBellCircuitRefinement
open QuantumCorrelatedPostNoise
open scoped BigOperators Matrix Kronecker ComplexOrder

-- A genuine 4-by-48 operator, with the environment and post-channel indices retained.
example (ss : List (Stage (FourIndex × Fin 3)))
    (post : BellMeasurement → CPTP PairIndex (Fin 2)) (model : Readout) (m r : BellMeasurement)
    (ij : (Paths ss × Fin 3) × Fin 2) : Matrix PairIndex (FourIndex × Fin 3) ℂ :=
  microKraus ss post model m r ij

-- CP is exercised on an additional three-dimensional spectator.
example (ss : List (Stage (FourIndex × Fin 2)))
    (post : BellMeasurement → CPTP PairIndex (Fin 2)) (model : Readout) (o : Outcome)
    (M : Matrix ((FourIndex × Fin 2) × Fin 3) ((FourIndex × Fin 2) × Fin 3) ℂ)
    (hM : M.PosSemidef) :
    (liftMapGen (Fin 3) (noisyJointOutcome ss post model o) M).PosSemidef :=
  noisy_outcome_cp ss post model o (Fin 3) M hM

-- Compatibility with the old 4-by-16 noisy instrument requires fixed product preparation.
example (ss : List (Stage (FourIndex × Fin 2))) (σ : EnvironmentState (Fin 2))
    (h : (ideal ss).matrix = extend (embedBC analysisUnitary))
    (post : BellMeasurement → CPTP PairIndex (Fin 2)) (model : Readout) (o : Outcome)
    (M : FourDensity) :
    noisyJointOutcome ss post model o (M ⊗ₖ σ.matrix) =
      noisyOutcome (QuantumMixedMemoryBSM.effectivePre ss σ) post model o M :=
  noisy_product_bridge ss σ h post model o M

example (ss : List (Stage (FourIndex × Fin 2)))
    (post : BellMeasurement → CPTP PairIndex (Fin 2)) (model : Readout) (o : Outcome)
    (N : JointFourDensity (Fin 2)) :
    noisyJointOutcome (ss ++ [QuantumPostBSMEnvironment.postStage]) post model o N =
      noisyJointOutcome ss post model o N := noisy_post_interaction_invariant ss post model o N

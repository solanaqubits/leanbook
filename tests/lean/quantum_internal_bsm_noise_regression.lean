import Verification.QuantumInternalBSMNoise

noncomputable section
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumLocalPostNoise QuantumNoisyVisibility
open scoped BigOperators ComplexOrder Matrix

-- Literal circuit orders; error location is part of the definition.
example {κ : Type} [Fintype κ] (E : CPTP FourIndex κ) (m : BellMeasurement) (k : κ) :
    internalReduction afterCNOT E m k =
      computationalReduction m * embedBC hadamardControl * E.op k * embedBC cnot := rfl

example {κ : Type} [Fintype κ] (E : CPTP FourIndex κ) (m : BellMeasurement) (k : κ) :
    internalReduction afterHadamard E m k =
      computationalReduction m * E.op k * embedBC analysisUnitary := by
  simp [internalReduction, afterHadamard, centralGate, analysisGate]

-- Generic four-qubit errors are conjugated, not assumed covariant.
example {κ : Type} [Fintype κ] (E : CPTP FourIndex κ) (m : BellMeasurement) (k : κ) :
    internalReduction afterCNOT E m k =
      reduction m * (effectivePre afterCNOT E).op k := internal_reduction_transport _ _ _ _

example (cut : CircuitCut) {κ : Type} [Fintype κ] (E : CPTP FourIndex κ)
    (model : Readout) (o : Outcome)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (hR : R.PosSemidef) :
    (liftMap 2 (internalOutcome cut E model o) R).PosSemidef :=
  internal_outcome_cp cut E model o 2 R hR

example (cut : CircuitCut) {κ : Type} [Fintype κ] (E : CPTP FourIndex κ)
    (model : Readout) (ρ : FourState) :
    (∑ o : Outcome, internalOutcome cut E model o ρ.matrix).trace = 1 := by
  rw [internal_total_trace, ρ.trace_one]

-- Rejection includes the same internal noise, with no correction chosen from a message.
example (cut : CircuitCut) {κ : Type} [Fintype κ] (E : CPTP FourIndex κ)
    (model : Readout) (ρ : FourState) :
    internalOutcome cut E model none ρ.matrix =
      lostMap model ((effectivePre cut E).map ρ.matrix) := internal_outcome_refinement _ _ _ _ _

-- Pair-isotropic noise commutes through either actual gate prefix, on every input matrix.
example (g : Visibility) (model : Readout) (o : Outcome) (M : FourDensity) :
    internalOutcome afterCNOT (centralChannel (depolarizing g)) model o M =
      internalOutcome afterHadamard (centralChannel (depolarizing g)) model o M := by
  rw [internal_depolarizing_outcome, internal_depolarizing_outcome]

example : (pullback cnotGate flipControlGate.channel).op () = flipBoth :=
  cnot_transports_control_flip_to_both

example : Complex.normSq ((hadamardControl * flipControl * cnot) (0,0) (0,0)) = 1/2 ∧
    Complex.normSq ((analysisUnitary * flipControl) (0,0) (0,0)) = 0 :=
  naive_noise_relocation_changes_born_probability

-- The old visibility law now applies to either internal cut, with local-D post-noise.
example (cut : CircuitCut) (bsm corr w v : Visibility) :
    internalAccepted cut (centralChannel (depolarizing bsm)) (fun _ => localDepolarizing corr)
      QuantumBellDiagonalSwapping.perfectReadout
      (inputDensity
        (QuantumBellDiagonalSwapping.isotropicDistribution w.val ⟨w.nonnegative,w.le_one⟩)
        (QuantumBellDiagonalSwapping.isotropicDistribution v.val ⟨v.nonnegative,v.le_one⟩)) =
      isotropic (multiplyVisibility corr (multiplyVisibility bsm (multiplyVisibility w v))) :=
  internal_local_visibility _ _ _ _ _

import Verification.QuantumMultiStageBSM

noncomputable section
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumMultiStageBSM QuantumLocalPostNoise QuantumNoisyVisibility
open scoped BigOperators ComplexOrder Matrix

-- Empty and singleton paths, and arbitrary chronological concatenation.
example (M : FourDensity) : run ([] : List (Stage FourIndex)) M = M := rfl
example (s : Stage FourIndex) (M : FourDensity) :
    (effective [s]).map M = (pullback s.gate s.noise).map M := singleton_effective s M
example (ss tt : List (Stage FourIndex)) (M : FourDensity) :
    run (ss ++ tt) M = run tt (run ss M) := run_append ss tt M

-- Distinct finite Kraus-index types at the two actual BSM positions.
example {κ ι : Type} [Fintype κ] [Fintype ι] (E : CPTP FourIndex κ) (F : CPTP FourIndex ι) :
    Fintype.card (Paths (bsmStages E F)) = Fintype.card κ * Fintype.card ι := by
  change Fintype.card (κ × (ι × Unit)) = _
  simp

example {κ ι : Type} [Fintype κ] [Fintype ι] (E : CPTP FourIndex κ) (F : CPTP FourIndex ι)
    (M : FourDensity) :
    (effective (bsmStages E F)).map M =
      (pullback (centralGate analysisGate) F).map
        ((pullback (centralGate cnotGate) E).map M) := bsm_effective_order E F M

example {κ ι : Type} [Fintype κ] [Fintype ι] (E : CPTP FourIndex κ) (F : CPTP FourIndex ι)
    (model : Readout) (o : Outcome)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (hR : R.PosSemidef) :
    (liftMap 2 (outcome (bsmStages E F) model o) R).PosSemidef :=
  QuantumMultiStageBSM.outcome_cp _ (bsm_ideal E F) model o 2 R hR

example {κ ι : Type} [Fintype κ] [Fintype ι] (E : CPTP FourIndex κ) (F : CPTP FourIndex ι)
    (model : Readout) (ρ : FourState) :
    (∑ o : Outcome, outcome (bsmStages E F) model o ρ.matrix).trace = 1 := by
  rw [total_trace _ (bsm_ideal E F), ρ.trace_one]

-- The rejection branch carries both noise channels, with no invented correction.
example {κ ι : Type} [Fintype κ] [Fintype ι] (E : CPTP FourIndex κ) (F : CPTP FourIndex ι)
    (model : Readout) (M : FourDensity) :
    outcome (bsmStages E F) model none M =
      lostMap model ((effective (bsmStages E F)).map M) := bsm_outcome_bridge E F model none M

-- Nonunitary channels witness noncommutativity on a valid normalized input.
example : qubitZero.PosSemidef ∧ qubitZero.trace = 1 := qubit_zero_valid
example : (compose (reset 1) (reset 0)).map qubitZero 1 1 = 1 ∧
    (compose (reset 0) (reset 1)).map qubitZero 1 1 = 0 := reset_order_changes_probability

def resetStage (t : Fin 2) : Stage (Fin 2) :=
  ⟨Fin 2, inferInstance, identityGate (Fin 2), reset t⟩
def idleStage : Stage (Fin 2) :=
  ⟨Unit, inferInstance, identityGate (Fin 2), identityChannel (Fin 2)⟩

-- A heterogeneous three-stage path is checked too, beyond the BSM specialization.
example : Fintype.card (Paths [resetStage 0, idleStage, resetStage 1]) = 4 := by
  change Fintype.card (Fin 2 × (Unit × (Fin 2 × Unit))) = 4
  simp
example (M : Matrix (Fin 2) (Fin 2) ℂ) :
    run [resetStage 0, idleStage, resetStage 1] M = (reset 1).map ((reset 0).map M) := by
  simp only [run, resetStage, idleStage, identityGate, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]
  change (reset 1).map ((identityChannel (Fin 2)).map ((reset 0).map M)) = _
  rw [identity_map]

-- On the explicit isotropic model, five visibility factors appear: g,h,corr,w,v.
def half : Visibility := ⟨1/2, by norm_num, by norm_num⟩
def zero : Visibility := ⟨0, by norm_num, by norm_num⟩

def input (w v : Visibility) : FourDensity := inputDensity
  (QuantumBellDiagonalSwapping.isotropicDistribution w.val ⟨w.nonnegative,w.le_one⟩)
  (QuantumBellDiagonalSwapping.isotropicDistribution v.val ⟨v.nonnegative,v.le_one⟩)

def output (g h corr w v : Visibility) : PairDensity :=
  accepted (bsmStages (centralChannel (depolarizing g)) (centralChannel (depolarizing h)))
    (fun _ => localDepolarizing corr) QuantumBellDiagonalSwapping.perfectReadout (input w v)

example : targetOverlap (output half half half half half) = (35/128 : ℂ) := by
  unfold output input
  rw [two_noise_local_visibility]
  simp [isotropic, QuantumBellDiagonalSwapping.density_overlap,
    QuantumBellDiagonalSwapping.isotropicDistribution, multiplyVisibility, half]
  norm_num

example (g corr w v : Visibility) : targetOverlap (output g zero corr w v) = (1/4 : ℂ) := by
  unfold output input
  rw [two_noise_local_visibility]
  simp [isotropic, QuantumBellDiagonalSwapping.density_overlap,
    QuantumBellDiagonalSwapping.isotropicDistribution, multiplyVisibility, zero]

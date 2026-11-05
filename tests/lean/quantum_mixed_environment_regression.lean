import Verification.QuantumMixedMemoryBSM

noncomputable section
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumBellCircuitRefinement QuantumGeneralBellReadout QuantumNoisyBellInstrument
open QuantumSwappingInstrument QuantumOutcomeInstrument QuantumGateNoiseComposition
open QuantumCentralDepolarization QuantumNoiseTransport QuantumOrderedNoiseComposition
open QuantumPersistentEnvironment QuantumEnvironmentExtension QuantumMixedEnvironment
open scoped BigOperators ComplexOrder Matrix Kronecker

-- An arbitrary mixed environment, not a disguised pure state.
def mixedEnv : EnvironmentState Bool where
  matrix := Matrix.diagonal (fun _ => (1/2 : ℂ))
  positive := Matrix.PosSemidef.diagonal (fun _ => by norm_num [Complex.le_def])
  trace_one := by simp [Matrix.trace, Matrix.diag]

def basisState (q : Bool) : EnvironmentState Bool where
  matrix := Matrix.diagonal (fun t => if t = q then 1 else 0)
  positive := Matrix.PosSemidef.diagonal (fun _ => by split_ifs <;> norm_num)
  trace_one := by simp [Matrix.trace, Matrix.diag]

-- Pure-basis compatibility includes singular density matrices.
example {κ : Type} [Fintype κ] (E : CPTP (Fin 3 × Bool) κ) (q : Bool)
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (mixedReduced E (basisState q)).map M = (reduced E q).map M := by
  apply pure_basis_limit
  intro a b
  simp [basisState, Matrix.diagonal_apply]
  split_ifs <;> simp_all

example (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (mixedReduced (identityChannel (Fin 3 × Bool)) mixedEnv).map M = M :=
  mixed_identity mixedEnv M

-- Two decompositions of the SAME maximally mixed state, in Z and X bases.
def xProjector (minus : Bool) : Matrix Bool Bool ℂ :=
  Matrix.of fun i j => if i = j then 1/2 else if minus then -1/2 else 1/2

-- Both X-basis ensemble components are positive normalized pure projectors.
example (minus : Bool) : (xProjector minus).PosSemidef := by
  let V : Matrix Bool Unit ℂ := Matrix.of fun i _ => if i && minus then -1 else 1
  have h : xProjector minus = (1/2 : ℝ) • (V * V.conjTranspose) := by
    ext i j : 2
    cases minus <;> cases i <;> cases j <;>
      norm_num [xProjector, V, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h]
  exact (Matrix.posSemidef_self_mul_conjTranspose V).smul (by norm_num)

example (minus : Bool) : (xProjector minus).trace = 1 ∧
    xProjector minus * xProjector minus = xProjector minus := by
  constructor
  · simp [xProjector, Matrix.trace, Matrix.diag]
  · ext i j : 2
    cases minus <;> cases i <;> cases j <;> norm_num [xProjector, Matrix.mul_apply]

example : mixedEnv.matrix =
    ∑ q : Bool, (1/2 : ℂ) • (basisState q).matrix := by
  ext i j : 2
  cases i <;> cases j <;> norm_num [mixedEnv, basisState,
    Matrix.diagonal_apply]

example : mixedEnv.matrix = ∑ q : Bool, (1/2 : ℂ) • xProjector q := by
  ext i j : 2
  cases i <;> cases j <;> norm_num [mixedEnv, xProjector,
    Matrix.diagonal_apply]

example {κ : Type} [Fintype κ] (E : CPTP (Fin 3 × Bool) κ)
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (∑ q : Bool, (1/2 : ℂ) • traceEnvironment (E.map (M ⊗ₖ (basisState q).matrix))) =
      ∑ q : Bool, (1/2 : ℂ) • traceEnvironment (E.map (M ⊗ₖ xProjector q)) := by
  have hz : mixedEnv.matrix = ∑ q : Bool, (1/2 : ℂ) • (basisState q).matrix := by
    ext i j : 2
    cases i <;> cases j <;> norm_num [mixedEnv, basisState,
      Matrix.diagonal_apply]
  have hx : mixedEnv.matrix = ∑ q : Bool, (1/2 : ℂ) • xProjector q := by
    ext i j : 2
    cases i <;> cases j <;> norm_num [mixedEnv, xProjector,
      Matrix.diagonal_apply]
  rw [← ensemble_semantics E mixedEnv _ _ hz, ensemble_semantics E mixedEnv _ _ hx]

-- Complete positivity on an entangled ancillary input, rather than only positivity.
example {κ : Type} [Fintype κ] (E : CPTP (Fin 3 × Bool) κ)
    (R : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) (hR : R.PosSemidef) :
    (Matrix.of fun a b : Fin 2 × Fin 3 =>
      (mixedReduced E mixedEnv).map
        (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2).PosSemidef :=
  (mixedReduced E mixedEnv).cp 2 R hR

example {κ : Type} [Fintype κ] (E : CPTP (Fin 3 × Bool) κ)
    (σ : EnvironmentState Bool) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    ((mixedReduced E σ).map M).trace = M.trace := (mixedReduced E σ).trace M

-- All five BSM outcomes retain trace balance for a mixed retained environment.
example {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP (FourIndex × Bool) κ) (F : CPTP (FourIndex × Bool) ι)
    (model : Readout) (M : FourDensity) :
    (∑ o : Outcome, QuantumMixedMemoryBSM.outcome (QuantumMemoryBSM.memoryStages E F)
      mixedEnv model o M).trace = M.trace :=
  QuantumMixedMemoryBSM.total_trace _ mixedEnv (QuantumMemoryBSM.memory_ideal E F) model M

example {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP (FourIndex × Bool) κ) (F : CPTP (FourIndex × Bool) ι)
    (model : Readout) (o : Outcome) (M : FourDensity) (hM : M.PosSemidef) :
    (QuantumMixedMemoryBSM.outcome (QuantumMemoryBSM.memoryStages E F)
      mixedEnv model o M).trace.re = 0 ↔
    QuantumMixedMemoryBSM.outcome (QuantumMemoryBSM.memoryStages E F)
      mixedEnv model o M = 0 :=
  QuantumMixedMemoryBSM.outcome_zero_iff _ mixedEnv
    (QuantumMemoryBSM.memory_ideal E F) model o M hM

example {κ ι : Type} [Fintype κ] [Fintype ι]
    (E : CPTP (FourIndex × Bool) κ) (F : CPTP (FourIndex × Bool) ι)
    (model : Readout) (o : Outcome)
    (R : Matrix (Fin 2 × FourIndex) (Fin 2 × FourIndex) ℂ) (hR : R.PosSemidef) :
    (liftMap 2 (QuantumMixedMemoryBSM.outcome (QuantumMemoryBSM.memoryStages E F)
      mixedEnv model o) R).PosSemidef :=
  QuantumMixedMemoryBSM.outcome_cp _ mixedEnv
    (QuantumMemoryBSM.memory_ideal E F) model o 2 R hR

-- An unused mixed environment creates neither spurious decoherence nor impossible outcomes.
example : QuantumMixedMemoryBSM.outcome
    (QuantumMemoryBSM.memoryStages (identityChannel (FourIndex × Bool))
      (identityChannel (FourIndex × Bool))) mixedEnv
    QuantumBellDiagonalSwapping.perfectReadout (some .psiPlus) ghzState.matrix = 0 := by
  rw [QuantumMixedMemoryBSM.memory_no_noise]
  exact QuantumNullConditioning.ghz_ideal_report_null.1

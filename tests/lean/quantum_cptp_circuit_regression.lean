import Verification.QuantumTwoQubitCPTP
import Verification.QuantumBellCircuitRefinement

open QuantumPauliMatrix QuantumPauliDensityBridge
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumTwoQubitCPTP QuantumBellCircuitRefinement
open scoped BigOperators ComplexOrder

private def fullNoise : BoundedBps := ⟨10000, by decide, by decide⟩
private def zeroNoise : BoundedBps := ⟨0, by decide, by decide⟩

example : Fintype.card (Option (PairIndex × PairIndex)) = 17 := by decide

example (p : BoundedBps) :
    ∑ k, (kraus p k).conjTranspose * kraus p k = (1 : PairDensity) :=
  kraus_completeness p

-- Off-diagonal, non-Hermitian input: the channel is defined on all matrices.
example : linearChannel fullNoise (matrixUnit (0,0) (1,1)) = 0 := by
  ext i j : 2
  simp [linearChannel, probability, fullNoise, Matrix.trace, Matrix.diag,
    matrixUnit]

-- A constant I/4 affine formula is not the linear channel on zero input.
example : linearChannel fullNoise 0 = 0 := by simp [linearChannel]
example : depolarizeMatrix fullNoise 0 ≠ linearChannel fullNoise 0 := by
  intro h
  have entry := congrArg (fun M : PairDensity => M (0,0) (0,0)) h
  norm_num [depolarizeMatrix, linearChannel, maximallyMixed, probability, fullNoise,
    Complex.real_smul] at entry

example (M : PairDensity) : linearChannel zeroNoise M = M := by
  simp [linearChannel, probability, zeroNoise]

example (d : Nat) (p : BoundedBps)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) (hR : R.PosSemidef) :
    (extension d p R).PosSemidef ∧ (extension d p R).trace = R.trace :=
  ⟨completely_positive d p R hR, extension_trace_preserving d p R⟩

-- Concrete entangled pure ancillary/system state, not just product inputs.
private noncomputable def entangled : (Fin 2 × PairIndex) → ℂ := fun x =>
  if x = (0,(0,0)) ∨ x = (1,(1,1)) then bellCoeff else 0

example (p : BoundedBps) :
    (extension 2 p (Matrix.vecMulVec entangled (star entangled))).PosSemidef := by
  exact completely_positive 2 p _ (Matrix.posSemidef_vecMulVec_self_star entangled)

example : analysisUnitary (outcomeBits .psiMinus) (1,0) = -bellCoeff := by
  rw [analysis_row]
  simp [bellKet]

-- All four gates/readout outcomes, for arbitrary incoming amplitudes.
example (m : BellMeasurement) (v : FourKet) :
    undoAnalysis (readoutProject m v) = swappingProject m v :=
  instrument_equals_bell_projection m v

example (m : BellMeasurement) : circuitProbability m swappingInput = (1 / 4 : ℝ) :=
  circuit_born_probability m

example (m : BellMeasurement) :
    correctOuter m ((2 : ℂ) • readoutBranch m swappingInput) = bellKet .phiPlus :=
  circuit_feedforward m

example (i : PairIndex) : basisEquiv.symm (basisEquiv i) = i := basisEquiv.symm_apply_apply i

example (m : BellMeasurement) (p : BoundedBps) :
    circuitProbability m swappingInput = (1 / 4 : ℝ) ∧
    targetOverlap (linearChannel p (circuitDensity m)) =
      1 - 3 * (probability p : ℂ) / 4 := circuit_then_cptp_fidelity m p

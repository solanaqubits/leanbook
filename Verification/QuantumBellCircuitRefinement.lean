/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumTwoQubitCPTP

/-! Ideal Bell measurement as CNOT, Hadamard on the control, and computational
readout. The measured central register is computational; undoing the analysis
unitary gives the Bell-projector instrument. No noisy detector is modeled. -/
noncomputable section
namespace QuantumBellCircuitRefinement
open QuantumPauliMatrix QuantumPauliDensityBridge
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumTwoQubitCPTP
open scoped BigOperators ComplexOrder

/-- Computational CNOT: (b,c) ↦ (b,b+c) in Fin 2. -/
def cnot : PairDensity := fun out inp =>
  if out.1 = inp.1 ∧ out.2 = inp.1 + inp.2 then 1 else 0

def hadamard : Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  if i = 1 ∧ j = 1 then -bellCoeff else bellCoeff

def hadamardControl : PairDensity := fun out inp =>
  hadamard out.1 inp.1 * if out.2 = inp.2 then 1 else 0

/-- Rightmost gate acts first. -/
def analysisUnitary : PairDensity := hadamardControl * cnot

def outcomeBits : BellMeasurement → PairIndex
  | .phiPlus => (0,0)
  | .phiMinus => (1,0)
  | .psiPlus => (0,1)
  | .psiMinus => (1,1)

/-- Explicit change from Fin-2 indices to the recursive Bool basis of v4.5. -/
def boolBasis (i : PairIndex) : Basis 2 := (i.1 == 1, i.2 == 1, ())

/-- The basis change covers all four computational basis vectors. -/
def basisEquiv : PairIndex ≃ Basis 2 where
  toFun := boolBasis
  invFun := fun b => (if b.1 then 1 else 0, if b.2.1 then 1 else 0)
  left_inv := by
    intro i
    rcases i with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;> rfl
  right_inv := by
    intro i
    rcases i with ⟨a,b,⟨⟩⟩
    cases a <;> cases b <;> rfl

theorem cnot_agrees_with_gaussian_matrix (i j : PairIndex) :
    cnot i j = embed cnotMatrix (boolBasis i) (boolBasis j) := by
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [cnot, embed, cnotMatrix, boolBasis, toComplex, go, gz]
  all_goals rfl

/-- Each analysis row is exactly a conjugated Bell ket, including Ψ− signs. -/
theorem analysis_row (m : BellMeasurement) (i : PairIndex) :
    analysisUnitary (outcomeBits m) i = star (bellKet m i.1 i.2) := by
  rcases i with ⟨b,c⟩
  cases m <;> fin_cases b <;> fin_cases c <;>
    simp [analysisUnitary, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      cnot, hadamardControl, hadamard, outcomeBits, bellKet]

theorem analysis_unitary_left : analysisUnitary.conjTranspose * analysisUnitary = 1 := by
  ext i j : 2
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [analysisUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, cnot, hadamardControl, hadamard] <;>
    ring_nf <;> norm_num [bellCoeff_sq]

theorem analysis_unitary_right : analysisUnitary * analysisUnitary.conjTranspose = 1 := by
  ext i j : 2
  rcases i with ⟨a,b⟩; rcases j with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [analysisUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, cnot, hadamardControl, hadamard] <;>
    ring_nf <;> norm_num [bellCoeff_sq]

/-- Execute the two central gates on an arbitrary four-qubit state. -/
def runCircuit (v : FourKet) : FourKet := fun a b c d =>
  ∑ i : PairIndex, analysisUnitary (b,c) i * v a i.1 i.2 d

/-- Unnormalized outer amplitude selected by a concrete computational outcome. -/
def readoutBranch (m : BellMeasurement) (v : FourKet) : PairKet := fun a d =>
  runCircuit v a (outcomeBits m).1 (outcomeBits m).2 d

theorem branch_equals_bell_contraction (m : BellMeasurement) (v : FourKet) :
    readoutBranch m v = swappingContraction m v := by
  funext a d
  simp [readoutBranch, runCircuit, analysis_row, swappingContraction, Fintype.sum_prod_type]

/-- Actual computational-basis projection after the analysis gates. -/
def readoutProject (m : BellMeasurement) (v : FourKet) : FourKet := fun a b c d =>
  if (b,c) = outcomeBits m then runCircuit v a b c d else 0

/-- Undo the analysis gates on the projected central register. -/
def undoAnalysis (v : FourKet) : FourKet := fun a b c d =>
  ∑ i : PairIndex, star (analysisUnitary i (b,c)) * v a i.1 i.2 d

theorem instrument_equals_bell_projection (m : BellMeasurement) (v : FourKet) :
    undoAnalysis (readoutProject m v) = swappingProject m v := by
  funext a b c d
  simp [undoAnalysis, readoutProject, mul_ite, analysis_row, swappingProject,
    ← branch_equals_bell_contraction, readoutBranch]

theorem readout_norm (m : BellMeasurement) (v : FourKet) :
    fourNormSq (readoutProject m v) = pairNormSq (readoutBranch m v) := by
  cases m <;>
    simp [fourNormSq, pairNormSq, readoutProject, readoutBranch, outcomeBits, Fin.sum_univ_two]

/-- Born probability computed from the actual computational projection. -/
def circuitProbability (m : BellMeasurement) (v : FourKet) : ℝ :=
  fourNormSq (readoutProject m v)

theorem circuit_born_probability (m : BellMeasurement) :
    circuitProbability m swappingInput = (1 / 4 : ℝ) := by
  rw [circuitProbability, readout_norm, branch_equals_bell_contraction,
    swapping_contraction_formula]
  cases m <;> norm_num [pairNormSq, bellKet, Fin.sum_univ_two, Complex.normSq_mul]

theorem circuit_feedforward (m : BellMeasurement) :
    correctOuter m ((2 : ℂ) • readoutBranch m swappingInput) = bellKet .phiPlus := by
  rw [branch_equals_bell_contraction]
  exact swapping_exact_correction m

/-- Normalized conditional outer density computed from the actual circuit branch. -/
def circuitDensity (m : BellMeasurement) : PairDensity :=
  purePairDensity (correctOuter m ((2 : ℂ) • readoutBranch m swappingInput))

theorem circuit_density_eq_corrected_state (m : BellMeasurement) :
    circuitDensity m = (correctedSwapState m).matrix := by
  unfold circuitDensity correctedSwapState swappedOuter
  rw [branch_equals_bell_contraction]

theorem circuit_density_valid (m : BellMeasurement) :
    (circuitDensity m).PosSemidef ∧ (circuitDensity m).trace = 1 := by
  rw [circuit_density_eq_corrected_state]
  exact ⟨(correctedSwapState m).positive, (correctedSwapState m).trace_one⟩

/-- Gate circuit, actual Born branch, feed-forward, and subsequent CPTP noise.
    The classical readout and gates are ideal; noise is applied only afterwards. -/
theorem circuit_then_cptp_fidelity (m : BellMeasurement) (p : BoundedBps) :
    circuitProbability m swappingInput = (1 / 4 : ℝ) ∧
    targetOverlap (linearChannel p (circuitDensity m)) =
      1 - 3 * (probability p : ℂ) / 4 := by
  refine ⟨circuit_born_probability m, ?_⟩
  rw [circuit_density_eq_corrected_state, state_map_agrees]
  exact (born_and_noisy_conditional_fidelity m p).2

/-- Registry interface for an ideal gate-level Bell analysis and readout. -/
structure QuantumBellCircuitRefinementSuite : Prop where
  gaussian_cnot : ∀ i j, cnot i j = embed cnotMatrix (boolBasis i) (boolBasis j)
  unitary : analysisUnitary.conjTranspose * analysisUnitary = 1 ∧
    analysisUnitary * analysisUnitary.conjTranspose = 1
  branch : ∀ m v, readoutBranch m v = swappingContraction m v
  instrument : ∀ m v, undoAnalysis (readoutProject m v) = swappingProject m v
  born : ∀ m, circuitProbability m swappingInput = (1 / 4 : ℝ)
  correction : ∀ m,
    correctOuter m ((2 : ℂ) • readoutBranch m swappingInput) = bellKet .phiPlus

  noisy_output : ∀ m p, circuitProbability m swappingInput = (1 / 4 : ℝ) ∧
    targetOverlap (linearChannel p (circuitDensity m)) = 1 - 3 * (probability p : ℂ) / 4

theorem verification_suite : QuantumBellCircuitRefinementSuite :=
  ⟨cnot_agrees_with_gaussian_matrix, ⟨analysis_unitary_left, analysis_unitary_right⟩,
    branch_equals_bell_contraction, instrument_equals_bell_projection,
    circuit_born_probability, circuit_feedforward, circuit_then_cptp_fidelity⟩

end QuantumBellCircuitRefinement

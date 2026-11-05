/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumSelectiveSwapping

/-! Independent Bell-diagonal input pairs. Pure-component swapping is derived
from the gate circuit, retaining phases at ket level. Density identities remove
only global phases, not arbitrary relative phases. -/
noncomputable section
namespace QuantumBellDiagonalInputs
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellCircuitRefinement
open QuantumNoisyBellInstrument QuantumNoisySwapping
open scoped BigOperators ComplexOrder Kronecker

def zBit : BellMeasurement → Bool
  | .phiPlus | .psiPlus => false
  | _ => true

def xBit : BellMeasurement → Bool
  | .phiPlus | .phiMinus => false
  | _ => true

def fromBits : Bool → Bool → BellMeasurement
  | false, false => .phiPlus
  | true, false => .phiMinus
  | false, true => .psiPlus
  | true, true => .psiMinus

def bellXor (a b : BellMeasurement) : BellMeasurement :=
  fromBits (xor (zBit a) (zBit b)) (xor (xBit a) (xBit b))

theorem xor_cancel (a b : BellMeasurement) : bellXor (bellXor a b) b = a := by
  cases a <;> cases b <;> rfl

theorem xor_zero_iff (a b : BellMeasurement) : bellXor a b = .phiPlus ↔ a = b := by
  cases a <;> cases b <;> decide

def productKet (a b : BellMeasurement) : FourKet := fun i j k l =>
  bellKet a i j * bellKet b k l

/-- The global sign is computed from the three Bell labels. -/
def branchNegative (a b m : BellMeasurement) : Bool :=
  xor (and (zBit b) (xor (xBit a) (xBit m))) (and (zBit m) (xBit a))

def signedHalf (negative : Bool) : ℂ := if negative then -(1 / 2) else 1 / 2

set_option maxHeartbeats 4000000 in
-- Checks 64 input/outcome triples at four outer amplitudes, including Ψ− phases.
theorem branch_amplitude (a b m : BellMeasurement) :
    readoutBranch m (productKet a b) =
      signedHalf (branchNegative a b m) • bellKet (bellXor (bellXor a b) m) := by
  rw [branch_equals_bell_contraction]
  funext i l
  cases a <;> cases b <;> cases m <;> fin_cases i <;> fin_cases l <;>
    simp [swappingContraction, productKet, bellKet, bellXor, fromBits,
      branchNegative, xBit, zBit, signedHalf] <;>
    ring_nf <;> norm_num [bellCoeff_cube]

theorem pair_norm_smul (c : ℂ) (v : PairKet) :
    pairNormSq (c • v) = Complex.normSq c * pairNormSq v := by
  simp [pairNormSq, Complex.normSq_mul]
  ring

theorem component_born_probability (a b m : BellMeasurement) :
    circuitProbability m (productKet a b) = (1 / 4 : ℝ) := by
  rw [circuitProbability, readout_norm, branch_amplitude, pair_norm_smul, bell_pair_normalized]
  cases h : branchNegative a b m <;> norm_num [signedHalf]

theorem correction_smul (r : BellMeasurement) (c : ℂ) (v : PairKet) :
    correctOuter r (c • v) = c • correctOuter r v := by
  funext i j
  cases r <;> fin_cases j <;> simp [correctOuter, amp, applyCorrection]

theorem signed_half_density (negative : Bool) (v : PairKet) :
    purePairDensity (signedHalf negative • v) = (1 / 4 : ℝ) • purePairDensity v := by
  ext i j : 2
  cases negative <;>
    simp [purePairDensity, Matrix.vecMulVec, signedHalf, Complex.real_smul] <;> ring

set_option maxHeartbeats 2000000 in
-- All sixteen Bell/correction combinations are compared at sixteen matrix entries.
theorem correction_density (a r : BellMeasurement) :
    purePairDensity (correctOuter r (bellKet a)) = bellProjector (bellXor a r) := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  cases a <;> cases r <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    simp [purePairDensity, Matrix.vecMulVec, correctOuter, amp, applyCorrection,
      bellKet, bellProjector, bellXor, fromBits, xBit, zBit]

theorem raw_corrected_density (a b m r : BellMeasurement) :
    purePairDensity (correctOuter r (readoutBranch m (productKet a b))) =
      (1 / 4 : ℝ) • bellProjector (bellXor (bellXor (bellXor a b) m) r) := by
  rw [branch_amplitude, correction_smul, signed_half_density, correction_density]

structure BellDistribution where
  weight : BellMeasurement → ℝ
  nonnegative : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

def density (p : BellDistribution) : PairDensity := ∑ a, p.weight a • bellProjector a

theorem density_positive (p : BellDistribution) : (density p).PosSemidef :=
  Matrix.posSemidef_sum _ fun a _ => (pure_pair_positive _).smul (p.nonnegative a)

theorem density_trace (p : BellDistribution) : (density p).trace = 1 := by
  simp only [density, Matrix.trace_sum, Matrix.trace_smul, bell_projector_trace]
  simpa using congrArg (fun x : ℝ => (x : ℂ)) p.total

def state (p : BellDistribution) : PairState :=
  ⟨density p, density_positive p, density_trace p⟩

abbrev FourIndex := PairIndex × PairIndex

def productDensity (a b : BellMeasurement) : Matrix FourIndex FourIndex ℂ :=
  let v := fun i : FourIndex => productKet a b i.1.1 i.1.2 i.2.1 i.2.2
  Matrix.vecMulVec v (star v)

theorem product_density_tensor (a b : BellMeasurement) :
    productDensity a b = bellProjector a ⊗ₖ bellProjector b := by
  ext i j : 2
  simp [productDensity, productKet, bellProjector, purePairDensity, Matrix.vecMulVec]
  ring

/-- Independent preparations: the joint weights are products p(a)q(b). -/
def inputDensity (p q : BellDistribution) : Matrix FourIndex FourIndex ℂ :=
  ∑ a, ∑ b, (p.weight a * q.weight b) • productDensity a b

theorem input_density_tensor (p q : BellDistribution) :
    inputDensity p q = density p ⊗ₖ density q := by
  ext i j : 2
  simp only [inputDensity, density, product_density_tensor, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kroneckerMap_apply, Complex.real_smul, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem input_positive (p q : BellDistribution) : (inputDensity p q).PosSemidef :=
  Matrix.posSemidef_sum _ fun a _ => Matrix.posSemidef_sum _ fun b _ =>
    (Matrix.posSemidef_vecMulVec_self_star _).smul (mul_nonneg (p.nonnegative a) (q.nonnegative b))

theorem input_trace (p q : BellDistribution) : (inputDensity p q).trace = 1 := by
  rw [input_density_tensor, Matrix.trace_kronecker, density_trace, density_trace, mul_one]

def mixedBornProbability (p q : BellDistribution) (m : BellMeasurement) : ℝ :=
  ∑ a, ∑ b, p.weight a * q.weight b * circuitProbability m (productKet a b)

theorem mixed_born_probability (p q : BellDistribution) (m : BellMeasurement) :
    mixedBornProbability p q m = 1 / 4 := by
  simp [mixedBornProbability, component_born_probability, mul_assoc,
    ← Finset.mul_sum, ← Finset.sum_mul, p.total, q.total]

structure QuantumBellDiagonalInputsSuite : Prop where
  amplitude : ∀ a b m, readoutBranch m (productKet a b) =
    signedHalf (branchNegative a b m) • bellKet (bellXor (bellXor a b) m)
  born : ∀ p q m, mixedBornProbability p q m = 1 / 4
  tensor : ∀ p q, inputDensity p q = density p ⊗ₖ density q
  input_valid : ∀ p q, (inputDensity p q).PosSemidef ∧ (inputDensity p q).trace = 1
  corrected_branch : ∀ a b m r,
    purePairDensity (correctOuter r (readoutBranch m (productKet a b))) =
      (1 / 4 : ℝ) • bellProjector (bellXor (bellXor (bellXor a b) m) r)

theorem verification_suite : QuantumBellDiagonalInputsSuite :=
  ⟨branch_amplitude, mixed_born_probability, input_density_tensor,
    fun p q => ⟨input_positive p q, input_trace p q⟩, raw_corrected_density⟩

end QuantumBellDiagonalInputs

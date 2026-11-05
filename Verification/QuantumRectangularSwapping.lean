/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBellDiagonalSwapping

/-! Rectangular Bell contractions and Pauli feed-forward on arbitrary four-qubit
amplitudes. Input basis is ((A,B),(C,D)); output basis is (A,D). -/
noncomputable section
namespace QuantumRectangularSwapping
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellCircuitRefinement
open QuantumNoisyBellInstrument QuantumBellDiagonalInputs QuantumBellDiagonalSwapping
open scoped BigOperators ComplexOrder Matrix

abbrev FourDensity := Matrix FourIndex FourIndex ℂ
abbrev BranchMatrix := Matrix PairIndex FourIndex ℂ

def flattenFour (v : FourKet) : FourIndex → ℂ := fun i => v i.1.1 i.1.2 i.2.1 i.2.2

def flattenPair (v : PairKet) : PairIndex → ℂ := fun i => v i.1 i.2

def pureFourDensity (v : FourKet) : FourDensity :=
  Matrix.vecMulVec (flattenFour v) (star (flattenFour v))

/-- Bra on BC, identity on A and D. -/
def reduction (m : BellMeasurement) : BranchMatrix := fun o i =>
  if o.1 = i.1.1 ∧ o.2 = i.2.2 then star (bellKet m i.1.2 i.2.1) else 0

def singleCorrection : BellMeasurement → Matrix (Fin 2) (Fin 2) ℂ
  | .phiPlus => 1
  | .phiMinus => fun i j => if i = j then (if i = 0 then 1 else -1) else 0
  | .psiPlus => fun i j => if i = j then 0 else 1
  | .psiMinus => fun i j => if i = j then 0 else (if i = 0 then 1 else -1)

def correction (r : BellMeasurement) : PairDensity := fun o i =>
  if o.1 = i.1 then singleCorrection r o.2 i.2 else 0

/-- L_{m,r}: a rectangular map from the four-qubit input to the outer pair. -/
def branchOperator (m r : BellMeasurement) : BranchMatrix := correction r * reduction m

theorem reduction_amplitudes (m : BellMeasurement) (v : FourKet) :
    reduction m *ᵥ flattenFour v = flattenPair (readoutBranch m v) := by
  rw [branch_equals_bell_contraction]
  funext o
  simp [reduction, flattenFour, flattenPair, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, ite_and, ite_mul, swappingContraction, eq_comm]

theorem correction_amplitudes (r : BellMeasurement) (v : PairKet) :
    correction r *ᵥ flattenPair v = flattenPair (correctOuter r v) := by
  funext o
  rcases o with ⟨a,d⟩
  cases r <;> fin_cases a <;> fin_cases d <;>
    simp [correction, singleCorrection, flattenPair, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, correctOuter, amp, applyCorrection]

theorem branch_amplitudes (m r : BellMeasurement) (v : FourKet) :
    branchOperator m r *ᵥ flattenFour v = flattenPair (correctOuter r (readoutBranch m v)) := by
  rw [branchOperator, ← Matrix.mulVec_mulVec, reduction_amplitudes, correction_amplitudes]

theorem correction_unitary (r : BellMeasurement) :
    (correction r).conjTranspose * correction r = 1 := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  cases r <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [correction, singleCorrection, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Lifted central Bell projector, independently defined by its entries. -/
def centralProjector (m : BellMeasurement) : FourDensity := fun i j =>
  if i.1.1 = j.1.1 ∧ i.2.2 = j.2.2 then
    bellKet m i.1.2 i.2.1 * star (bellKet m j.1.2 j.2.1) else 0

theorem reduction_effect (m : BellMeasurement) :
    (reduction m).conjTranspose * reduction m = centralProjector m := by
  ext i j : 2
  simp [reduction, centralProjector, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ite_and, mul_ite, eq_comm]
  split_ifs <;> simp_all

theorem branch_effect (m r : BellMeasurement) :
    (branchOperator m r).conjTranspose * branchOperator m r = centralProjector m := by
  unfold branchOperator
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (reduction m).conjTranspose *
        ((correction r).conjTranspose * correction r) * reduction m := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [correction_unitary, Matrix.mul_one, reduction_effect]

theorem central_projector_positive (m : BellMeasurement) : (centralProjector m).PosSemidef := by
  rw [← reduction_effect]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem bell_completeness (b c b' c' : Fin 2) :
    (∑ m, bellKet m b c * star (bellKet m b' c')) =
      if b = b' ∧ c = c' then 1 else 0 := by
  rw [sum_bell]
  fin_cases b <;> fin_cases c <;> fin_cases b' <;> fin_cases c' <;>
    norm_num [bellKet, ← pow_two, bellCoeff_sq]

theorem central_completeness : (∑ m, centralProjector m) = (1 : FourDensity) := by
  ext i j : 2
  simp only [centralProjector, Matrix.sum_apply, Finset.sum_ite_irrel,
    Finset.sum_const_zero, bell_completeness, Matrix.one_apply]
  by_cases h : i = j
  · subst j; simp
  · have hn : ¬ (i.1.1 = j.1.1 ∧ i.1.2 = j.1.2 ∧ i.2.1 = j.2.1 ∧ i.2.2 = j.2.2) := by
      intro heq
      exact h (Prod.ext (Prod.ext heq.1 heq.2.1) (Prod.ext heq.2.2.1 heq.2.2.2))
    simp only [h, if_false]
    split_ifs <;> aesop

theorem sandwich_pure (L : BranchMatrix) (v : FourIndex → ℂ) :
    L * Matrix.vecMulVec v (star v) * L.conjTranspose =
      Matrix.vecMulVec (L *ᵥ v) (star (L *ᵥ v)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [Matrix.vecMul_conjTranspose, star_star]

theorem branch_pure_density (m r : BellMeasurement) (v : FourKet) :
    branchOperator m r * pureFourDensity v * (branchOperator m r).conjTranspose =
      purePairDensity (correctOuter r (readoutBranch m v)) := by
  rw [pureFourDensity, sandwich_pure, branch_amplitudes]
  rfl

theorem component_refinement (a b m r : BellMeasurement) :
    branchOperator m r * productDensity a b * (branchOperator m r).conjTranspose =
      (1 / 4 : ℝ) • bellProjector (bellXor (bellXor (bellXor a b) m) r) := by
  change branchOperator m r * pureFourDensity (productKet a b) *
    (branchOperator m r).conjTranspose = _
  rw [branch_pure_density, raw_corrected_density]

theorem sandwich_trace (L : BranchMatrix) (M : FourDensity) :
    (L * M * L.conjTranspose).trace = (L.conjTranspose * L * M).trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]

structure QuantumRectangularSwappingSuite : Prop where
  amplitudes : ∀ m r v,
    branchOperator m r *ᵥ flattenFour v = flattenPair (correctOuter r (readoutBranch m v))
  effect : ∀ m r, (branchOperator m r).conjTranspose * branchOperator m r = centralProjector m
  complete : (∑ m, centralProjector m) = (1 : FourDensity)
  pure_bridge : ∀ m r v,
    branchOperator m r * pureFourDensity v * (branchOperator m r).conjTranspose =
      purePairDensity (correctOuter r (readoutBranch m v))
  bell_bridge : ∀ a b m r,
    branchOperator m r * productDensity a b * (branchOperator m r).conjTranspose =
      (1 / 4 : ℝ) • bellProjector (bellXor (bellXor (bellXor a b) m) r)

theorem verification_suite : QuantumRectangularSwappingSuite :=
  ⟨branch_amplitudes, branch_effect, central_completeness, branch_pure_density,
    component_refinement⟩

end QuantumRectangularSwapping

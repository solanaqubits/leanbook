/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCascadedSwapping

/-! A finite local ensemble: Pauli dephasing followed by a three-cycle Clifford.
The target is Phi+, so Bob applies the complex conjugate of Alice's gate. -/
noncomputable section
namespace QuantumCliffordTwirl
open QuantumCorrelatedMemoryBSM QuantumBellDiagonalInputs QuantumNoisyBellInstrument
open QuantumStateAvailabilityContract QuantumEntanglementSwappingPurificationContract
open QuantumPauliDensityBridge QuantumBellDiagonalSwapping
open scoped BigOperators ComplexOrder Matrix Kronecker

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def cycleGate : QubitMatrix := !![(1-Complex.I)/2, (-1-Complex.I)/2;
  (1-Complex.I)/2, (1+Complex.I)/2]

def localPair (U : QubitMatrix) : PairDensity := U ⊗ₖ U.map star

def pairCycle : PairDensity := localPair cycleGate

theorem cycle_unitary : cycleGate.conjTranspose * cycleGate = 1 := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [cycleGate, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num [Complex.I_sq]

def pauli (p : PairIndex) : QubitMatrix := fun i j =>
  if j = i + p.1 then (if i = 1 ∧ p.2 = 1 then -1 else 1) else 0

def pauliPair (p : PairIndex) : PairDensity := localPair (pauli p)

def pauliTwirl (M : PairDensity) : PairDensity :=
  weightedFamily (fun _ : PairIndex => (1 / 4 : ℝ)) pauliPair M

def cycleTwirl (M : PairDensity) : PairDensity :=
  (1 / 3 : ℂ) • (M + pairCycle * M * pairCycle.conjTranspose +
    (pairCycle * pairCycle) * M * (pairCycle * pairCycle).conjTranspose)

def twirl (M : PairDensity) : PairDensity := cycleTwirl (pauliTwirl M)

def permute : BellMeasurement → BellMeasurement
  | .phiPlus => .phiPlus
  | .phiMinus => .psiPlus
  | .psiPlus => .psiMinus
  | .psiMinus => .phiMinus

def bellSign (a : BellMeasurement) (i : PairIndex) : ℂ :=
  match a with
  | .phiPlus => if i.1 = i.2 then 1 else 0
  | .phiMinus => if i.1 = i.2 then (if i.1 = 0 then 1 else -1) else 0
  | .psiPlus => if i.1 ≠ i.2 then 1 else 0
  | .psiMinus => if i.1 ≠ i.2 then (if i.1 = 0 then 1 else -1) else 0

theorem projector_entry (a : BellMeasurement) (i j : PairIndex) :
    bellProjector a i j = (1 / 2 : ℂ) * bellSign a i * bellSign a j := by
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  cases a <;> fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [bellProjector, purePairDensity, Matrix.vecMulVec, bellKet, bellSign] <;>
    ring_nf <;> norm_num [bellCoeff_sq]

theorem cycle_phiPlus :
    pairCycle * bellProjector .phiPlus * pairCycle.conjTranspose =
      bellProjector (permute .phiPlus) := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pairCycle, localPair, cycleGate, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, projector_entry, bellSign, permute] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem cycle_phiMinus :
    pairCycle * bellProjector .phiMinus * pairCycle.conjTranspose =
      bellProjector (permute .phiMinus) := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pairCycle, localPair, cycleGate, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, projector_entry, bellSign, permute] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem cycle_psiPlus :
    pairCycle * bellProjector .psiPlus * pairCycle.conjTranspose =
      bellProjector (permute .psiPlus) := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pairCycle, localPair, cycleGate, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, projector_entry, bellSign, permute] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem cycle_psiMinus :
    pairCycle * bellProjector .psiMinus * pairCycle.conjTranspose =
      bellProjector (permute .psiMinus) := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pairCycle, localPair, cycleGate, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, projector_entry, bellSign, permute] <;>
    ring_nf <;> norm_num [Complex.I_sq]

theorem cycle_projector (a : BellMeasurement) :
    pairCycle * bellProjector a * pairCycle.conjTranspose = bellProjector (permute a) := by
  cases a
  · exact cycle_phiPlus
  · exact cycle_phiMinus
  · exact cycle_psiPlus
  · exact cycle_psiMinus



theorem pauli_unitary (p : PairIndex) : (pauli p).conjTranspose * pauli p = 1 := by
  ext i j : 2
  rcases p with ⟨x,z⟩
  fin_cases x <;> fin_cases z <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Fin.add_def]

def bellMass (M : PairDensity) (a : BellMeasurement) : ℂ :=
  (bellProjector a * M).trace

theorem pauli_dephasing_row0 (M : PairDensity) (j : PairIndex) :
    pauliTwirl M (0,0) j = (∑ a, bellMass M a • bellProjector a) (0,0) j := by
  rcases j with ⟨j0,j1⟩
  fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pauliTwirl, weightedFamily, pauliPair, localPair, pauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.add_def, sum_bell, bellMass, Matrix.trace, Matrix.diag,
      projector_entry, bellSign] <;> ring

theorem pauli_dephasing_row1 (M : PairDensity) (j : PairIndex) :
    pauliTwirl M (0,1) j = (∑ a, bellMass M a • bellProjector a) (0,1) j := by
  rcases j with ⟨j0,j1⟩
  fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pauliTwirl, weightedFamily, pauliPair, localPair, pauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.add_def, sum_bell, bellMass, Matrix.trace, Matrix.diag,
      projector_entry, bellSign] <;> ring

theorem pauli_dephasing_row2 (M : PairDensity) (j : PairIndex) :
    pauliTwirl M (1,0) j = (∑ a, bellMass M a • bellProjector a) (1,0) j := by
  rcases j with ⟨j0,j1⟩
  fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pauliTwirl, weightedFamily, pauliPair, localPair, pauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.add_def, sum_bell, bellMass, Matrix.trace, Matrix.diag,
      projector_entry, bellSign] <;> ring

theorem pauli_dephasing_row3 (M : PairDensity) (j : PairIndex) :
    pauliTwirl M (1,1) j = (∑ a, bellMass M a • bellProjector a) (1,1) j := by
  rcases j with ⟨j0,j1⟩
  fin_cases j0 <;> fin_cases j1 <;>
    norm_num [pauliTwirl, weightedFamily, pauliPair, localPair, pauli,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.add_def, sum_bell, bellMass, Matrix.trace, Matrix.diag,
      projector_entry, bellSign] <;> ring

theorem pauli_dephasing (M : PairDensity) :
    pauliTwirl M = ∑ a, bellMass M a • bellProjector a := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩
  fin_cases i0 <;> fin_cases i1
  · exact pauli_dephasing_row0 M j
  · exact pauli_dephasing_row1 M j
  · exact pauli_dephasing_row2 M j
  · exact pauli_dephasing_row3 M j

theorem bellMass_total (M : PairDensity) : ∑ a, bellMass M a = M.trace := by
  simp [bellMass, sum_bell, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, projector_entry, bellSign]
  ring

theorem target_bellMass (M : PairDensity) : bellMass M .phiPlus = targetOverlap M := by
  simp [bellMass, Matrix.trace, Matrix.diag, Matrix.mul_apply, targetOverlap,
    Fintype.sum_prod_type, Fin.sum_univ_two, projector_entry, bellSign, bellKet]
  ring_nf
  norm_num [bellCoeff_sq]

theorem cycle_twirl_projector (a : BellMeasurement) :
    cycleTwirl (bellProjector a) =
      if a = .phiPlus then bellProjector .phiPlus else
        (1 / 3 : ℂ) • (bellProjector .phiMinus + bellProjector .psiPlus +
          bellProjector .psiMinus) := by
  have h : (pairCycle * pairCycle) * bellProjector a *
      (pairCycle * pairCycle).conjTranspose = bellProjector (permute (permute a)) := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = pairCycle * (pairCycle * bellProjector a * pairCycle.conjTranspose) *
        pairCycle.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [cycle_projector, cycle_projector]
  rw [cycleTwirl, cycle_projector, h]
  cases a <;> simp [permute]
  all_goals module

theorem cycle_twirl_sum (f : BellMeasurement → ℂ) :
    cycleTwirl (∑ a, f a • bellProjector a) = ∑ a, f a • cycleTwirl (bellProjector a) := by
  simp only [cycleTwirl, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.sum_add_distrib, Finset.smul_sum, smul_add, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  module

theorem twirl_formula (M : PairDensity) :
    twirl M = targetOverlap M • bellProjector .phiPlus +
      ((M.trace - targetOverlap M) / 3) •
        (bellProjector .phiMinus + bellProjector .psiPlus + bellProjector .psiMinus) := by
  rw [twirl, pauli_dephasing, cycle_twirl_sum]
  simp only [cycle_twirl_projector, sum_bell]
  have h := bellMass_total M
  rw [sum_bell, target_bellMass] at h
  simp only [target_bellMass]
  simp only [↓reduceIte, reduceCtorEq, one_div, smul_add]
  rw [← h]
  module



theorem cycle_family (M : PairDensity) :
    cycleTwirl M = weightedFamily (fun _ : Fin 3 => (1 / 3 : ℝ))
      (fun k => pairCycle ^ k.val) M := by
  simp [weightedFamily, Fin.sum_univ_succ, cycleTwirl, pow_two, smul_add, add_assoc]

theorem cp_comp {n m p : Type}
    (f : Matrix m m ℂ → Matrix p p ℂ) (g : Matrix n n ℂ → Matrix m m ℂ)
    (hf : IsCPMap f) (hg : IsCPMap g) : IsCPMap (fun M => f (g M)) := by
  intro a _ _ M hM
  exact hf a (liftMapGen a g M) (hg a M hM)

theorem twirl_cp : IsCPMap twirl := by
  apply cp_comp cycleTwirl pauliTwirl
  · have h : cycleTwirl = weightedFamily (fun _ : Fin 3 => (1 / 3 : ℝ))
        (fun k => pairCycle ^ k.val) := funext cycle_family
    rw [h]
    exact weightedFamily_cp _ (fun _ => by norm_num) _
  · exact weightedFamily_cp _ (fun _ => by norm_num) _

theorem twirl_trace (M : PairDensity) : (twirl M).trace = M.trace := by
  rw [twirl_formula]
  simp [Matrix.trace_add, Matrix.trace_smul, QuantumNoisySwapping.bell_projector_trace]
  ring

theorem twirl_overlap (M : PairDensity) : targetOverlap (twirl M) = targetOverlap M := by
  rw [twirl_formula]
  simp only [targetOverlap]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, add_mul,
    Finset.sum_add_distrib]
  -- Use linearity over complex scalars, then the four projector overlaps.
  all_goals
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, projector_entry, bellSign, bellKet]
    ring_nf
    norm_num [bellCoeff_sq, bellCoeff_four]
    ring

theorem twirl_add (M N : PairDensity) : twirl (M+N) = twirl M + twirl N := by
  simp only [twirl, pauliTwirl, weightedFamily_add, cycle_family]

theorem twirl_smul (c : ℂ) (M : PairDensity) : twirl (c • M) = c • twirl M := by
  simp only [twirl, pauliTwirl, weightedFamily_smul, cycle_family]



theorem localPair_mul (U V : QubitMatrix) : localPair (U*V) = localPair U * localPair V := by
  change (U*V) ⊗ₖ (U*V).map (starRingEnd ℂ) =
    (U ⊗ₖ U.map (starRingEnd ℂ)) * (V ⊗ₖ V.map (starRingEnd ℂ))
  rw [Matrix.map_mul, Matrix.mul_kronecker_mul]

/-- The three-cycle normalizes the Pauli matrices, with explicit phases. -/
theorem cycle_clifford (x z : Fin 2) :
    cycleGate * pauli (x,z) * cycleGate.conjTranspose =
      (if x = 0 then 1 else if z = 0 then -Complex.I else Complex.I) •
        pauli (x+z,x) := by
  ext i j : 2
  fin_cases x <;> fin_cases z <;> fin_cases i <;> fin_cases j <;>
    norm_num [cycleGate, pauli, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Fin.add_def] <;> ring_nf <;> norm_num [Complex.I_sq]

theorem bell_complete :
    bellProjector .phiPlus + bellProjector .phiMinus + bellProjector .psiPlus +
      bellProjector .psiMinus = 1 := by
  ext i j : 2
  rcases i with ⟨i0,i1⟩; rcases j with ⟨j0,j1⟩
  fin_cases i0 <;> fin_cases i1 <;> fin_cases j0 <;> fin_cases j1 <;>
    norm_num [projector_entry, bellSign, Matrix.one_apply]

theorem twirl_isotropic_formula (M : PairDensity) :
    twirl M = targetOverlap M • bellProjector .phiPlus +
      ((M.trace-targetOverlap M)/3) • (1-bellProjector .phiPlus) := by
  rw [twirl_formula, ← bell_complete]
  congr 2
  abel



structure QuantumCliffordTwirlSuite : Prop where
  complete_positivity : IsCPMap twirl
  trace : ∀ M, (twirl M).trace = M.trace
  fidelity : ∀ M, targetOverlap (twirl M) = targetOverlap M
  isotropic : ∀ M, twirl M = targetOverlap M • bellProjector .phiPlus +
    ((M.trace-targetOverlap M)/3) • (1-bellProjector .phiPlus)

theorem verification_suite : QuantumCliffordTwirlSuite :=
  ⟨twirl_cp, twirl_trace, twirl_overlap, twirl_isotropic_formula⟩

end QuantumCliffordTwirl

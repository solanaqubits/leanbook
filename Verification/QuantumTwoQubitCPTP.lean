/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPauliDensityBridge
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! A trace-preserving linear extension of the two-qubit depolarizing state map.
The mixing probability is bounded. Complete positivity is quantified over every
finite ancillary dimension and proved using an independently defined block map. -/
noncomputable section
namespace QuantumTwoQubitCPTP
open QuantumPauliMatrix QuantumPauliDensityBridge
open QuantumEntanglementSwappingPurificationContract
open scoped BigOperators ComplexOrder Kronecker

/-- Matrix unit |i⟩⟨j| on the two-qubit computational basis. -/
def matrixUnit (i j : PairIndex) : PairDensity :=
  fun a b => if a = i ∧ b = j then 1 else 0

theorem unit_sandwich (i j : PairIndex) (M : PairDensity) :
    matrixUnit i j * M * (matrixUnit i j).conjTranspose =
      M j j • matrixUnit i i := by
  ext a b : 2
  simp [matrixUnit, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ite_and, mul_ite, ite_mul, eq_comm, apply_ite (starRingEnd ℂ)]
  split_ifs <;> rfl

theorem unit_sum (M : PairDensity) :
    (∑ i, ∑ j, matrixUnit i j * M * (matrixUnit i j).conjTranspose) =
      M.trace • (1 : PairDensity) := by
  simp only [unit_sandwich]
  ext a b : 2
  simp [Matrix.sum_apply, matrixUnit, Matrix.trace, Matrix.one_apply, ite_and, eq_comm]

theorem unit_adjoint (i j : PairIndex) :
    (matrixUnit i j).conjTranspose = matrixUnit j i := by
  ext a b : 2
  simp [matrixUnit, Matrix.conjTranspose_apply, and_comm]

theorem unit_reverse_product (i j : PairIndex) :
    matrixUnit j i * matrixUnit i j = matrixUnit j j := by
  ext a b : 2
  simp [matrixUnit, Matrix.mul_apply, ite_and, mul_ite, eq_comm]
  split_ifs <;> rfl

theorem diagonal_unit_sum : (∑ j, matrixUnit j j) = (1 : PairDensity) := by
  ext a b : 2
  simp [Matrix.sum_apply, matrixUnit, Matrix.one_apply, ite_and, eq_comm]

/-- One identity Kraus operator and sixteen reset operators. -/
def kraus (p : BoundedBps) : Option (PairIndex × PairIndex) → PairDensity
  | none => (Real.sqrt (1 - probability p) : ℂ) • 1
  | some (i,j) => (Real.sqrt (probability p / 4) : ℂ) • matrixUnit i j

def krausMap (p : BoundedBps) (M : PairDensity) : PairDensity :=
  ∑ k, kraus p k * M * (kraus p k).conjTranspose

/-- Linear on all matrices, unlike an affine formula with a constant I/4 term. -/
def linearChannel (p : BoundedBps) (M : PairDensity) : PairDensity :=
  ((1 - probability p : ℝ) : ℂ) • M +
    ((probability p / 4 : ℝ) : ℂ) • (M.trace • (1 : PairDensity))

theorem sqrt_sandwich (r : ℝ) (hr : 0 ≤ r) (A M : PairDensity) :
    ((Real.sqrt r : ℂ) • A) * M * ((Real.sqrt r : ℂ) • A).conjTranspose =
      (r : ℂ) • (A * M * A.conjTranspose) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hr]

theorem kraus_exact (p : BoundedBps) (M : PairDensity) :
    krausMap p M = linearChannel p M := by
  unfold krausMap
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [kraus]
  rw [sqrt_sandwich _ (sub_nonneg.mpr (probability_bounds p).2)]
  have hp : 0 ≤ probability p / 4 := div_nonneg (probability_bounds p).1 (by norm_num)
  simp_rw [sqrt_sandwich (probability p / 4) hp]
  simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    ← Finset.smul_sum, unit_sum]
  rfl

theorem kraus_none_norm (p : BoundedBps) :
    (kraus p none).conjTranspose * kraus p none =
      ((1 - probability p : ℝ) : ℂ) • (1 : PairDensity) := by
  simp only [kraus, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul]
  rw [← pow_two, ← Complex.ofReal_pow,
    Real.sq_sqrt (sub_nonneg.mpr (probability_bounds p).2)]

theorem kraus_some_norm (p : BoundedBps) (i j : PairIndex) :
    (kraus p (some (i,j))).conjTranspose * kraus p (some (i,j)) =
      ((probability p / 4 : ℝ) : ℂ) • matrixUnit j j := by
  simp only [kraus, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    unit_adjoint, Matrix.smul_mul, Matrix.mul_smul, smul_smul, unit_reverse_product]
  rw [← pow_two, ← Complex.ofReal_pow,
    Real.sq_sqrt (div_nonneg (probability_bounds p).1 (by norm_num))]

theorem kraus_completeness (p : BoundedBps) :
    ∑ k, (kraus p k).conjTranspose * kraus p k = (1 : PairDensity) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [kraus_none_norm, kraus_some_norm, ← Finset.smul_sum, diagonal_unit_sum]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_ofNat, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Nat.reduceMul, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  ext i j : 2
  by_cases h : i = j <;> simp [Matrix.ofNat_apply, Matrix.one_apply, h]

theorem linearChannel_trace (p : BoundedBps) (M : PairDensity) :
    (linearChannel p M).trace = M.trace := by
  simp [linearChannel, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  ring

theorem linearChannel_add (p : BoundedBps) (M N : PairDensity) :
    linearChannel p (M + N) = linearChannel p M + linearChannel p N := by
  simp [linearChannel, Matrix.trace_add, smul_add, add_smul]
  abel

theorem linearChannel_smul (p : BoundedBps) (c : ℂ) (M : PairDensity) :
    linearChannel p (c • M) = c • linearChannel p M := by
  ext i j : 2
  simp [linearChannel, Matrix.trace_smul, smul_smul]
  ring

theorem state_map_agrees (p : BoundedBps) (ρ : PairState) :
    linearChannel p ρ.matrix = (depolarize p ρ).matrix := by
  ext i j : 2
  simp [linearChannel, depolarize, depolarizeMatrix, maximallyMixed,
    ρ.trace_one, Complex.real_smul, smul_smul]
  ring_nf
  simp

/-- Independent definition of id_d ⊗ Dλ by its matrix blocks. -/
def extension (d : Nat) (p : BoundedBps)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) :
    Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ := fun a b =>
  linearChannel p (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2

theorem extension_kraus (d : Nat) (p : BoundedBps)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) :
    extension d p R = ∑ k,
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ kraus p k) * R *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ kraus p k).conjTranspose := by
  ext a b : 2
  change linearChannel p (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2 = _
  rw [← kraus_exact]
  simp [krausMap, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Matrix.one_apply,
    apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_add_distrib]

theorem completely_positive (d : Nat) (p : BoundedBps)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) (hR : R.PosSemidef) :
    (extension d p R).PosSemidef := by
  rw [extension_kraus]
  exact Matrix.posSemidef_sum _ fun _ _ => hR.mul_mul_conjTranspose_same _

theorem extension_trace_preserving (d : Nat) (p : BoundedBps)
    (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ) :
    (extension d p R).trace = R.trace := by
  simp only [Matrix.trace, Matrix.diag, extension, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Matrix.of_apply] using
    linearChannel_trace p (Matrix.of fun i j => R (a,i) (a,j))


/-- Registry interface for a concrete CPTP map and its normalized-state bridge. -/
structure QuantumTwoQubitCPTPSuite : Prop where
  kraus_formula : ∀ p M, krausMap p M = linearChannel p M
  completeness : ∀ p, ∑ k, (kraus p k).conjTranspose * kraus p k = (1 : PairDensity)
  trace_preserving : ∀ p M, (linearChannel p M).trace = M.trace
  state_bridge : ∀ p (ρ : PairState), linearChannel p ρ.matrix = (depolarize p ρ).matrix
  cp : ∀ d p (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ),
    R.PosSemidef → (extension d p R).PosSemidef
  extended_trace : ∀ d p (R : Matrix (Fin d × PairIndex) (Fin d × PairIndex) ℂ),
    (extension d p R).trace = R.trace

theorem verification_suite : QuantumTwoQubitCPTPSuite :=
  ⟨kraus_exact, kraus_completeness, linearChannel_trace, state_map_agrees,
    completely_positive, extension_trace_preserving⟩

end QuantumTwoQubitCPTP

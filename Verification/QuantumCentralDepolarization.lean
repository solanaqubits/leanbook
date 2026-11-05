/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumGateNoiseComposition
import Verification.QuantumTwoQubitCPTP

/-! Real-visibility depolarization and a local lift to the central pair BC.
The pre channel acts before the ideal Bell contraction, not at an unspecified gate location. -/
noncomputable section
namespace QuantumCentralDepolarization
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumSwappingInstrument QuantumGateNoiseComposition
open QuantumTwoQubitCPTP (matrixUnit unit_sandwich unit_sum unit_adjoint
  unit_reverse_product diagonal_unit_sum)
open scoped BigOperators ComplexOrder Kronecker Matrix

structure Visibility where
  val : ℝ
  nonnegative : 0 ≤ val
  le_one : val ≤ 1

def probability (v : Visibility) : ℝ := 1 - v.val

theorem probability_bounds (v : Visibility) : 0 ≤ probability v ∧ probability v ≤ 1 := by
  unfold probability
  constructor <;> linarith [v.nonnegative, v.le_one]

/-- One identity Kraus operator and sixteen reset operators. -/
def kraus (p : Visibility) : Option (PairIndex × PairIndex) → PairDensity
  | none => (Real.sqrt (1 - probability p) : ℂ) • 1
  | some (i,j) => (Real.sqrt (probability p / 4) : ℂ) • matrixUnit i j

def krausMap (p : Visibility) (M : PairDensity) : PairDensity :=
  ∑ k, kraus p k * M * (kraus p k).conjTranspose

/-- Linear on all matrices, unlike an affine formula with a constant I/4 term. -/
def linearChannel (p : Visibility) (M : PairDensity) : PairDensity :=
  ((1 - probability p : ℝ) : ℂ) • M +
    ((probability p / 4 : ℝ) : ℂ) • (M.trace • (1 : PairDensity))

theorem sqrt_sandwich (r : ℝ) (hr : 0 ≤ r) (A M : PairDensity) :
    ((Real.sqrt r : ℂ) • A) * M * ((Real.sqrt r : ℂ) • A).conjTranspose =
      (r : ℂ) • (A * M * A.conjTranspose) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hr]

theorem kraus_exact (p : Visibility) (M : PairDensity) :
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

theorem kraus_none_norm (p : Visibility) :
    (kraus p none).conjTranspose * kraus p none =
      ((1 - probability p : ℝ) : ℂ) • (1 : PairDensity) := by
  simp only [kraus, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul]
  rw [← pow_two, ← Complex.ofReal_pow,
    Real.sq_sqrt (sub_nonneg.mpr (probability_bounds p).2)]

theorem kraus_some_norm (p : Visibility) (i j : PairIndex) :
    (kraus p (some (i,j))).conjTranspose * kraus p (some (i,j)) =
      ((probability p / 4 : ℝ) : ℂ) • matrixUnit j j := by
  simp only [kraus, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    unit_adjoint, Matrix.smul_mul, Matrix.mul_smul, smul_smul, unit_reverse_product]
  rw [← pow_two, ← Complex.ofReal_pow,
    Real.sq_sqrt (div_nonneg (probability_bounds p).1 (by norm_num))]

theorem kraus_completeness (p : Visibility) :
    ∑ k, (kraus p k).conjTranspose * kraus p k = (1 : PairDensity) := by
  rw [Fintype.sum_option, Fintype.sum_prod_type]
  simp only [kraus_none_norm, kraus_some_norm, ← Finset.smul_sum, diagonal_unit_sum]
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
    Complex.ofReal_ofNat, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Nat.reduceMul, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  ext i j : 2
  by_cases h : i = j <;> simp [Matrix.ofNat_apply, Matrix.one_apply, h]

theorem linearChannel_trace (p : Visibility) (M : PairDensity) :
    (linearChannel p M).trace = M.trace := by
  simp [linearChannel, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  ring

theorem linearChannel_add (p : Visibility) (M N : PairDensity) :
    linearChannel p (M + N) = linearChannel p M + linearChannel p N := by
  simp [linearChannel, Matrix.trace_add, smul_add, add_smul]
  abel

theorem linearChannel_smul (p : Visibility) (c : ℂ) (M : PairDensity) :
    linearChannel p (c • M) = c • linearChannel p M := by
  ext i j : 2
  simp [linearChannel, Matrix.trace_smul, smul_smul]
  ring

def depolarizing (v : Visibility) : CPTP PairIndex (Option (PairIndex × PairIndex)) :=
  ⟨kraus v, kraus_completeness v⟩

theorem depolarizing_map (v : Visibility) (M : PairDensity) :
    (depolarizing v).map M = (v.val : ℂ) • M +
      (((1 - v.val) / 4 : ℝ) : ℂ) • (M.trace • (1 : PairDensity)) := by
  change krausMap v M = _
  rw [kraus_exact]
  simp [linearChannel, probability]

/-- Isotropic pair depolarization commutes with unitary conjugation on that same pair. -/
theorem depolarizing_covariance (v : Visibility) (U M : PairDensity)
    (hleft : U.conjTranspose * U = 1) (hright : U * U.conjTranspose = 1) :
    (depolarizing v).map (U * M * U.conjTranspose) =
      U * (depolarizing v).map M * U.conjTranspose := by
  have ht : (U * M * U.conjTranspose).trace = M.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hleft, Matrix.one_mul]
  rw [depolarizing_map, depolarizing_map, ht]
  simp [Matrix.mul_add, Matrix.add_mul, hright]

/-- I_A ⊗ T_BC ⊗ I_D in the ((A,B),(C,D)) indexing convention. -/
def embedBC (T : PairDensity) : FourDensity := fun i j =>
  if i.1.1 = j.1.1 ∧ i.2.2 = j.2.2 then T (i.1.2,i.2.1) (j.1.2,j.2.1) else 0

theorem embedBC_adjoint (T : PairDensity) :
    (embedBC T).conjTranspose = embedBC T.conjTranspose := by
  ext i j : 2
  simp [embedBC, Matrix.conjTranspose_apply, eq_comm, apply_ite (starRingEnd ℂ)]

theorem embedBC_mul (T S : PairDensity) : embedBC T * embedBC S = embedBC (T * S) := by
  ext i j : 2
  simp [embedBC, Matrix.mul_apply, Fintype.sum_prod_type, ite_and, mul_ite, ite_mul, eq_comm]

@[simp] theorem embedBC_one : embedBC 1 = (1 : FourDensity) := by
  ext i j : 2
  simp [embedBC, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem embedBC_sum {α : Type*} [Fintype α] (T : α → PairDensity) :
    embedBC (∑ a, T a) = ∑ a, embedBC (T a) := by
  ext i j : 2
  simp [embedBC, Matrix.sum_apply]

variable {κ : Type*} [Fintype κ]

def centralChannel (E : CPTP PairIndex κ) : CPTP FourIndex κ where
  op := fun k => embedBC (E.op k)
  complete := by
    simp only [embedBC_adjoint, embedBC_mul, ← embedBC_sum, E.complete, embedBC_one]

theorem central_map (E : CPTP PairIndex κ) (M : FourDensity) (i j : FourIndex) :
    (centralChannel E).map M i j =
      E.map (Matrix.of fun b c => M ((i.1.1,b.1),(b.2,i.2.2))
        ((j.1.1,c.1),(c.2,j.2.2))) (i.1.2,i.2.1) (j.1.2,j.2.1) := by
  simp [CPTP.map, centralChannel, embedBC, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, ite_and, mul_ite, ite_mul,
    eq_comm, apply_ite (starRingEnd ℂ)]

def traceBC (M : FourDensity) : PairDensity := fun i j =>
  ∑ b : Fin 2, ∑ c : Fin 2, M ((i.1,b),(c,i.2)) ((j.1,b),(c,j.2))

theorem central_depolarizing_entry (v : Visibility) (M : FourDensity) (i j : FourIndex) :
    (centralChannel (depolarizing v)).map M i j =
      (v.val : ℂ) * M i j + (((1 - v.val) / 4 : ℝ) : ℂ) *
        (if i.1.2 = j.1.2 ∧ i.2.1 = j.2.1 then traceBC M (i.1.1,i.2.2) (j.1.1,j.2.2) else 0) := by
  rw [central_map, depolarizing_map]
  simp [Matrix.smul_apply, Matrix.one_apply, Matrix.trace, Matrix.diag,
    Fintype.sum_prod_type, traceBC, Prod.ext_iff]

theorem bell_left_marginal (a : BellMeasurement) (i j : Fin 2) :
    (∑ k, bellKet a i k * star (bellKet a j k)) = if i = j then (1 / 2 : ℂ) else 0 := by
  cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [bellKet, Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

theorem bell_right_marginal (a : BellMeasurement) (i j : Fin 2) :
    (∑ k, bellKet a k i * star (bellKet a k j)) = if i = j then (1 / 2 : ℂ) else 0 := by
  cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [bellKet, Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

theorem traceBC_product (a b : BellMeasurement) :
    traceBC (productDensity a b) = (1 / 4 : ℂ) • (1 : PairDensity) := by
  ext i j : 2
  have hf : traceBC (productDensity a b) i j =
      (∑ k, bellKet a i.1 k * star (bellKet a j.1 k)) *
      (∑ k, bellKet b k i.2 * star (bellKet b k j.2)) := by
    simp only [traceBC, productDensity, productKet, Matrix.vecMulVec, Pi.star_apply,
      star_mul, Matrix.of_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hf, bell_left_marginal, bell_right_marginal]
  simp [Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all
  all_goals norm_num

def traceBCLinear : FourDensity →ₗ[ℂ] PairDensity where
  toFun := traceBC
  map_add' := by intro M N; ext i j : 2; simp [traceBC, Finset.sum_add_distrib]
  map_smul' := by intro c M; ext i j : 2; simp [traceBC]; ring

theorem traceBC_sum {α : Type*} [Fintype α] (M : α → FourDensity) :
    traceBC (∑ a, M a) = ∑ a, traceBC (M a) := map_sum traceBCLinear M Finset.univ

theorem traceBC_real_smul (c : ℝ) (M : FourDensity) : traceBC (c • M) = c • traceBC M := by
  ext i j : 2
  simp [traceBC]

theorem traceBC_input (p q : BellDistribution) :
    traceBC (inputDensity p q) = (1 / 4 : ℂ) • (1 : PairDensity) := by
  simp only [inputDensity, traceBC_sum, traceBC_real_smul, traceBC_product,
    ← Finset.sum_smul, ← Finset.mul_sum, q.total, mul_one, p.total, one_smul]

def fullyMixedFour : FourDensity := (1 / 16 : ℂ) • 1

theorem central_input_depolarization (v : Visibility) (p q : BellDistribution) :
    (centralChannel (depolarizing v)).map (inputDensity p q) =
      (v.val : ℂ) • inputDensity p q + ((1 - v.val : ℝ) : ℂ) • fullyMixedFour := by
  ext i j : 2
  rw [central_depolarizing_entry, traceBC_input]
  simp [fullyMixedFour, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all
  all_goals ring

/-- A deterministic bit flip on C is a CPTP pre-error, not classical message confusion. -/
def flipCentralC : CPTP FourIndex Unit := centralChannel
  ⟨(fun _ => correction .psiPlus), by simpa using correction_unitary .psiPlus⟩

def flippedGHZKet : FourKet := fun a b c d =>
  if a = b ∧ b ≠ c ∧ a = d then bellCoeff else 0

theorem flip_ghz_density : flipCentralC.map ghzState.matrix = pureFourDensity flippedGHZKet := by
  have hv : embedBC (correction .psiPlus) *ᵥ flattenFour ghzKet =
      flattenFour flippedGHZKet := by
    funext i
    rcases i with ⟨⟨a,b⟩,⟨c,d⟩⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [embedBC, correction, singleCorrection, Matrix.mulVec, dotProduct,
        flattenFour, ghzKet, flippedGHZKet, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [CPTP.map, flipCentralC, centralChannel, Fintype.sum_unique, ghzState,
    pureFourDensity]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star, hv]

theorem pre_flip_opens_ghz_branch :
    bornProbability .psiPlus ghzState = 0 ∧
    bornProbability .psiPlus (noiseState flipCentralC ghzState) = 1 / 2 := by
  refine ⟨ghz_born_probabilities .psiPlus, ?_⟩
  unfold bornProbability noiseState
  dsimp only
  rw [flip_ghz_density, pureFourDensity, sandwich_pure, reduction_amplitudes]
  change (purePairDensity
    (QuantumBellCircuitRefinement.readoutBranch .psiPlus flippedGHZKet)).trace.re = _
  rw [pure_pair_trace, QuantumBellCircuitRefinement.branch_equals_bell_contraction]
  norm_num [pairNormSq, swappingContraction, flippedGHZKet, bellKet,
    Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

structure QuantumCentralDepolarizationSuite : Prop where
  exact_map : ∀ v M, (depolarizing v).map M = (v.val : ℂ) • M +
    (((1 - v.val) / 4 : ℝ) : ℂ) • (M.trace • (1 : PairDensity))
  central_input : ∀ v p q,
    (centralChannel (depolarizing v)).map (inputDensity p q) =
      (v.val : ℂ) • inputDensity p q + ((1 - v.val : ℝ) : ℂ) • fullyMixedFour
  ghz_change : bornProbability .psiPlus ghzState = 0 ∧
    bornProbability .psiPlus (noiseState flipCentralC ghzState) = 1 / 2

theorem verification_suite : QuantumCentralDepolarizationSuite :=
  ⟨depolarizing_map, central_input_depolarization, pre_flip_opens_ghz_branch⟩

end QuantumCentralDepolarization

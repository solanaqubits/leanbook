/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoisyVisibility
import Verification.QuantumDepolarizingChannel

/-! Local CPTP noise on D preserves the A marginal. Local and pair depolarization
are different maps; their agreement requires a maximally mixed A marginal. -/
noncomputable section
namespace QuantumLocalPostNoise
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumGateNoiseComposition QuantumCentralDepolarization
open scoped BigOperators ComplexOrder Kronecker Matrix

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def embedD (T : QubitMatrix) : PairDensity := fun i j =>
  if i.1 = j.1 then T i.2 j.2 else 0

theorem embedD_adjoint (T : QubitMatrix) : (embedD T).conjTranspose = embedD T.conjTranspose := by
  ext i j : 2
  simp [embedD, Matrix.conjTranspose_apply, eq_comm, apply_ite (starRingEnd ℂ)]

theorem embedD_mul (T S : QubitMatrix) : embedD T * embedD S = embedD (T * S) := by
  ext i j : 2
  simp [embedD, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, ite_mul, eq_comm]

@[simp] theorem embedD_one : embedD 1 = (1 : PairDensity) := by
  ext i j : 2
  simp [embedD, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem embedD_sum {α : Type*} [Fintype α] (T : α → QubitMatrix) :
    embedD (∑ a, T a) = ∑ a, embedD (T a) := by
  ext i j : 2
  simp [embedD, Matrix.sum_apply]

variable {κ : Type*} [Fintype κ]

def onD (E : CPTP (Fin 2) κ) : CPTP PairIndex κ where
  op := fun k => embedD (E.op k)
  complete := by
    simp only [embedD_adjoint, embedD_mul, ← embedD_sum, E.complete, embedD_one]

theorem onD_map (E : CPTP (Fin 2) κ) (M : PairDensity) (i j : PairIndex) :
    (onD E).map M i j = E.map (Matrix.of fun d e => M (i.1,d) (j.1,e)) i.2 j.2 := by
  simp [CPTP.map, onD, embedD, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, mul_ite, ite_mul,
    eq_comm, apply_ite (starRingEnd ℂ)]

/-- Partial trace over D, retaining the state of A. -/
def traceD (M : PairDensity) : QubitMatrix := fun a b => ∑ d, M (a,d) (b,d)

theorem onD_preserves_A (E : CPTP (Fin 2) κ) (M : PairDensity) :
    traceD ((onD E).map M) = traceD M := by
  ext a b : 2
  simp only [traceD, onD_map]
  exact E.trace (Matrix.of fun d e => M (a,d) (b,e))

/-- Total nonidentity-Pauli probability, not the mixing weight 1-γ. -/
def pauliError (v : Visibility) : ℝ := 3 * (1 - v.val) / 4

theorem pauli_error_physical (v : Visibility) :
    QuantumDepolarizingChannel.Physical (pauliError v) := by
  unfold QuantumDepolarizingChannel.Physical pauliError
  constructor <;> linarith [v.nonnegative, v.le_one]

def qubitDepolarizing (v : Visibility) : CPTP (Fin 2) (Fin 4) :=
  ⟨QuantumDepolarizingChannel.K (pauliError v),
    QuantumDepolarizingChannel.kraus_completeness _ (pauli_error_physical v)⟩

theorem qubit_depolarizing_map (v : Visibility) (M : QubitMatrix) :
    (qubitDepolarizing v).map M = (v.val : ℂ) • M +
      (((1 - v.val) / 2 : ℝ) : ℂ) • (M.trace • (1 : QubitMatrix)) := by
  change QuantumDepolarizingChannel.depolarizingChannel (pauliError v) M = _
  rw [QuantumDepolarizingChannel.depolarizing_exact _ (pauli_error_physical v)]
  have hs : QuantumDepolarizingChannel.shrink (pauliError v) = v.val := by
    unfold QuantumDepolarizingChannel.shrink pauliError
    ring
  have hp : 2 * pauliError v / 3 = (1 - v.val) / 2 := by unfold pauliError; ring
  rw [hs, hp]

def localDepolarizing (v : Visibility) : CPTP PairIndex (Fin 4) := onD (qubitDepolarizing v)

theorem local_depolarizing_entry (v : Visibility) (M : PairDensity) (i j : PairIndex) :
    (localDepolarizing v).map M i j = (v.val : ℂ) * M i j +
      (((1 - v.val) / 2 : ℝ) : ℂ) * (if i.2 = j.2 then traceD M i.1 j.1 else 0) := by
  rw [localDepolarizing, onD_map, qubit_depolarizing_map]
  simp [Matrix.smul_apply, Matrix.one_apply, traceD, Matrix.trace, Matrix.diag]

theorem local_depolarizing_formula (v : Visibility) (M : PairDensity) :
    (localDepolarizing v).map M = (v.val : ℂ) • M +
      (((1 - v.val) / 2 : ℝ) : ℂ) • (traceD M ⊗ₖ (1 : QubitMatrix)) := by
  ext i j : 2
  rw [local_depolarizing_entry]
  simp [Matrix.one_apply]

theorem local_depolarizing_preserves_A (v : Visibility) (M : PairDensity) :
    traceD ((localDepolarizing v).map M) = traceD M := onD_preserves_A _ M

/-- Exact sufficient condition, valid even for subnormalized/nonpositive input matrices. -/
theorem local_equals_pair_of_marginal (v : Visibility) (M : PairDensity)
    (hM : traceD M = (M.trace / 2) • (1 : QubitMatrix)) :
    (localDepolarizing v).map M = (depolarizing v).map M := by
  ext i j : 2
  rw [local_depolarizing_entry, depolarizing_map, hM]
  simp [Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all
  all_goals ring

/-- Away from the identity endpoint, the same marginal condition is also necessary. -/
theorem local_equals_pair_iff (v : Visibility) (hv : v.val < 1) (M : PairDensity) :
    (localDepolarizing v).map M = (depolarizing v).map M ↔
      traceD M = (M.trace / 2) • (1 : QubitMatrix) := by
  constructor
  · intro h
    ext a b : 2
    have he := congrArg (fun N : PairDensity => N (a,0) (b,0)) h
    rw [local_depolarizing_entry, depolarizing_map] at he
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Prod.mk.injEq, and_true, ite_true, mul_ite, mul_one, mul_zero] at he ⊢
    have hc : ((1 - v.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hv))
    have hz : ((1 - v.val : ℝ) : ℂ) *
        (traceD M a b - M.trace / 2 * (if a = b then 1 else 0)) = 0 := by
      push_cast at he ⊢
      split_ifs at he ⊢ <;> linear_combination 2 * he
    simpa only [mul_ite, mul_one, mul_zero] using
      sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)
  · exact local_equals_pair_of_marginal v M

structure QuantumLocalPostNoiseSuite : Prop where
  marginal_invariant : ∀ {κ : Type} [Fintype κ] (E : CPTP (Fin 2) κ) M,
    traceD ((onD E).map M) = traceD M
  local_formula : ∀ v M,
    (localDepolarizing v).map M = (v.val : ℂ) • M +
      (((1 - v.val) / 2 : ℝ) : ℂ) • (traceD M ⊗ₖ (1 : QubitMatrix))
  agreement_iff : ∀ v, v.val < 1 → ∀ M,
    (localDepolarizing v).map M = (depolarizing v).map M ↔
      traceD M = (M.trace / 2) • (1 : QubitMatrix)

theorem verification_suite : QuantumLocalPostNoiseSuite :=
  ⟨onD_preserves_A, local_depolarizing_formula, local_equals_pair_iff⟩

end QuantumLocalPostNoise

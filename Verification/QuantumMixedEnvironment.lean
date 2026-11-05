/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumEnvironmentExtension
import Mathlib.Analysis.Matrix.Order

/-! A fixed arbitrary finite density matrix for an initially independent environment.
A square-root factor supplies Kraus preparation; its operational semantics depends
only on the density matrix, not on a chosen ensemble. -/
noncomputable section
namespace QuantumMixedEnvironment
open QuantumGateNoiseComposition QuantumPersistentEnvironment QuantumEnvironmentExtension
open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker

variable {n o e κ : Type} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e]

structure EnvironmentState (e : Type) [Fintype e] where
  matrix : Matrix e e ℂ
  positive : matrix.PosSemidef
  trace_one : matrix.trace = 1

/-- Canonical factor exists also for singular states; no inverse or full-rank assumption. -/
def factor (σ : EnvironmentState e) : Matrix e e ℂ := CFC.sqrt σ.matrix

theorem factor_product (σ : EnvironmentState e) :
    factor σ * (factor σ).conjTranspose = σ.matrix := by
  have h := (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg σ.matrix)).isHermitian
  rw [factor, h.eq, CFC.sqrt_mul_sqrt_self σ.matrix σ.positive.nonneg]

/-- One preparation Kraus operator per column of the square-root factor. -/
def prepareOp (σ : EnvironmentState e) (t : e) : Matrix (n × e) n ℂ :=
  Matrix.of fun a i => if a.1 = i then factor σ a.2 t else 0

theorem prepare_op_sandwich (σ : EnvironmentState e) (t : e) (M : Matrix n n ℂ)
    (a b : n × e) :
    (prepareOp (n := n) σ t * M * (prepareOp (n := n) σ t).conjTranspose) a b =
      M a.1 b.1 * (factor σ a.2 t * star (factor σ b.2 t)) := by
  simp [prepareOp, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite, ite_mul]
  ring

/-- Preparation is exactly tensoring with the supplied mixed state. -/
theorem preparation_semantics (σ : EnvironmentState e) (M : Matrix n n ℂ) :
    (∑ t, prepareOp (n := n) σ t * M * (prepareOp (n := n) σ t).conjTranspose) = M ⊗ₖ σ.matrix := by
  ext a b : 2
  simp only [Matrix.sum_apply, prepare_op_sandwich, ← Finset.mul_sum,
    Matrix.kroneckerMap_apply]
  have h := congrFun (congrFun (factor_product σ) a.2) b.2
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using congrArg (M a.1 b.1 * ·) h

theorem preparation_complete (σ : EnvironmentState e) :
    (∑ t, (prepareOp (n := n) σ t).conjTranspose * prepareOp (n := n) σ t) = 1 := by
  have entry (t : e) (i j : n) :
      ((prepareOp (n := n) σ t).conjTranspose * prepareOp (n := n) σ t) i j =
        if i = j then ∑ a, star (factor σ a t) * factor σ a t else 0 := by
    simp [prepareOp, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, apply_ite, ite_mul, eq_comm]
    split_ifs <;> simp_all
  ext i j : 2
  simp only [Matrix.sum_apply, entry]
  by_cases hij : i = j
  · subst j
    simp only [if_true, Matrix.one_apply_eq]
    have h := congrArg Matrix.trace (factor_product σ)
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply] at h
    rw [Finset.sum_comm]
    simpa only [mul_comm] using h.trans σ.trace_one
  · simp [hij]

omit [Fintype n] [DecidableEq n] [DecidableEq e] in
theorem trace_tensor_state (σ : EnvironmentState e) (M : Matrix n n ℂ) :
    traceEnvironment (M ⊗ₖ σ.matrix) = M := by
  ext i j : 2
  change (∑ t, M i j * σ.matrix t t) = M i j
  rw [← Finset.mul_sum]
  change M i j * σ.matrix.trace = M i j
  rw [σ.trace_one, mul_one]

variable [Fintype κ]

/-- Reduced system channel: prepare once, evolve jointly, discard final environment. -/
def mixedReduced (E : CPTP (n × e) κ) (σ : EnvironmentState e) : CPTP n (e × κ × e) where
  op tkr := select (n := n) tkr.2.2 * E.op tkr.2.1 * prepareOp (n := n) σ tkr.1
  complete := by
    simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul]
    calc
      _ = ∑ t : e, ∑ k : κ, (prepareOp (n := n) σ t).conjTranspose * (E.op k).conjTranspose *
          (∑ r : e, (select (n := n) r).conjTranspose * select (n := n) r) * E.op k *
          prepareOp σ t := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = ∑ t : e, (prepareOp (n := n) σ t).conjTranspose *
          (∑ k, (E.op k).conjTranspose * E.op k) * prepareOp σ t := by
        simp only [selectors_complete, Matrix.mul_one, Matrix.mul_sum, Matrix.sum_mul,
          Matrix.mul_assoc]
      _ = 1 := by simp only [E.complete, Matrix.mul_one, preparation_complete]

variable [Fintype o] [DecidableEq o]

/-- Arbitrary rectangular branches, without a completeness assumption on the joint family. -/
theorem mixed_branch_partial_trace (K : κ → Matrix (o × e) (n × e) ℂ)
    (σ : EnvironmentState e) (M : Matrix n n ℂ) :
    traceEnvironment (∑ k, K k * (M ⊗ₖ σ.matrix) * (K k).conjTranspose) =
      ∑ tkr : e × κ × e,
        (select (n := o) tkr.2.2 * K tkr.2.1 * prepareOp (n := n) σ tkr.1) * M *
        (select (n := o) tkr.2.2 * K tkr.2.1 * prepareOp (n := n) σ tkr.1).conjTranspose := by
  rw [← preparation_semantics σ M, trace_environment_family]
  simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_assoc]
  conv_lhs => arg 2; ext r; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.sum_comm

theorem mixed_reduced_map (E : CPTP (n × e) κ) (σ : EnvironmentState e)
    (M : Matrix n n ℂ) :
    (mixedReduced E σ).map M = traceEnvironment (E.map (M ⊗ₖ σ.matrix)) := by
  simp only [CPTP.map]
  rw [mixed_branch_partial_trace]
  rfl

/-- Any ensemble or factorization with the same density produces exactly the same output. -/
theorem density_extensionality (E : CPTP (n × e) κ) (σ τ : EnvironmentState e)
    (h : σ.matrix = τ.matrix) (M : Matrix n n ℂ) :
    (mixedReduced E σ).map M = (mixedReduced E τ).map M := by
  rw [mixed_reduced_map, mixed_reduced_map, h]

/-- Linear extension of any supplied ensemble equality; nonnegative normalized
weights are required to interpret it as a physical ensemble, not for this algebraic identity. -/
theorem ensemble_semantics {ι : Type} [Fintype ι] (E : CPTP (n × e) κ)
    (σ : EnvironmentState e) (c : ι → ℂ) (τ : ι → Matrix e e ℂ)
    (h : σ.matrix = ∑ t, c t • τ t) (M : Matrix n n ℂ) :
    (mixedReduced E σ).map M =
      ∑ t, c t • traceEnvironment (E.map (M ⊗ₖ τ t)) := by
  have ht : M ⊗ₖ σ.matrix = ∑ t, c t • (M ⊗ₖ τ t) := by
    rw [h]
    ext a b : 2
    simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum, mul_left_comm]
  rw [mixed_reduced_map, ht, CPTP.map_sum, trace_environment_sum]
  simp only [CPTP.map_smul, trace_environment_smul]

theorem mixed_identity (σ : EnvironmentState e) (M : Matrix n n ℂ) :
    (mixedReduced (identityChannel (n × e)) σ).map M = M := by
  rw [mixed_reduced_map, identity_map, trace_tensor_state]

/-- Recover the earlier pure-basis preparation whenever its tensor matrix agrees. -/
theorem pure_basis_limit (E : CPTP (n × e) κ) (σ : EnvironmentState e) (q : e)
    (h : ∀ a b, σ.matrix a b = if a = q ∧ b = q then 1 else 0) (M : Matrix n n ℂ) :
    (mixedReduced E σ).map M = (reduced E q).map M := by
  rw [mixed_reduced_map, reduced_map]
  have hp : M ⊗ₖ σ.matrix = prepare q M := by
    ext a b : 2
    rw [Matrix.kronecker_apply, h, prepare_entry]
    split_ifs <;> simp
  rw [hp]

structure QuantumMixedEnvironmentSuite : Prop where
  semantics : ∀ {κ : Type} [Fintype κ] (E : CPTP (Fin 4 × Fin 2) κ)
    (σ : EnvironmentState (Fin 2)) M,
    (mixedReduced E σ).map M = traceEnvironment (E.map (M ⊗ₖ σ.matrix))
  identity : ∀ (σ : EnvironmentState (Fin 2)) (M : Matrix (Fin 4) (Fin 4) ℂ),
    (mixedReduced (identityChannel (Fin 4 × Fin 2)) σ).map M = M

theorem verification_suite : QuantumMixedEnvironmentSuite := ⟨mixed_reduced_map, mixed_identity⟩

end QuantumMixedEnvironment

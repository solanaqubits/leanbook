/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPersistentEnvironment

/-! Rectangular system operators extended by an untouched finite environment.
Branchwise environment elimination is an algebraic partial-trace identity. -/
noncomputable section
namespace QuantumEnvironmentExtension
open QuantumGateNoiseComposition QuantumNoiseTransport QuantumPersistentEnvironment
open scoped BigOperators ComplexOrder Kronecker Matrix

variable {n o t e κ : Type} [DecidableEq e]

def extend (A : Matrix o n ℂ) : Matrix (o × e) (n × e) ℂ := A ⊗ₖ (1 : Matrix e e ℂ)

theorem extend_adjoint (A : Matrix o n ℂ) :
    (extend (e := e) A).conjTranspose = extend A.conjTranspose := by
  simp [extend, Matrix.conjTranspose_kronecker]

theorem extend_mul [Fintype n] [Fintype e] (A : Matrix o n ℂ) (B : Matrix n t ℂ) :
    extend (e := e) A * extend B = extend (A * B) := by
  unfold extend
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]

theorem extend_one [DecidableEq n] : extend (e := e) (1 : Matrix n n ℂ) = 1 :=
  Matrix.one_kronecker_one

variable [Fintype n] [DecidableEq n] [Fintype o] [DecidableEq o] [Fintype e]

def extendGate (U : UnitaryGate n) : UnitaryGate (n × e) where
  matrix := extend U.matrix
  left := by rw [extend_adjoint, extend_mul, U.left, extend_one]
  right := by rw [extend_adjoint, extend_mul, U.right, extend_one]

theorem select_extend (A : Matrix o n ℂ) (q : e) :
    select (n := o) q * extend A = A * select (n := n) q := by
  ext i j : 2
  simp [select, QuantumPersistentEnvironment.insert, extend, Matrix.mul_apply,
    Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply,
    ite_and, apply_ite, ite_mul, eq_comm]
  split_ifs <;> simp_all

theorem extend_insert (A : Matrix o n ℂ) (q : e) :
    extend A * insert (n := n) q = insert (n := o) q * A := by
  have h := congrArg Matrix.conjTranspose (select_extend A.conjTranspose q)
  simpa only [Matrix.conjTranspose_mul, extend_adjoint, Matrix.conjTranspose_conjTranspose,
    select] using h

omit [DecidableEq n] [DecidableEq o] [Fintype o] in
/-- Pulling out an operator that acts only on the retained system. -/
theorem trace_environment_sandwich [Finite o] (A : Matrix o n ℂ)
    (M : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment (extend A * M * (extend A).conjTranspose) =
      A * traceEnvironment M * A.conjTranspose := by
  classical
  let := Fintype.ofFinite o
  rw [trace_environment_family, trace_environment_family]
  have h (q : e) :
      select (n := o) q * (extend A * M * (extend A).conjTranspose) *
        (select (n := o) q).conjTranspose =
      A * (select (n := n) q * M * (select (n := n) q).conjTranspose) * A.conjTranspose := by
    calc
      select (n := o) q * (extend A * M * (extend A).conjTranspose) *
          (select (n := o) q).conjTranspose =
        (select (n := o) q * extend (e := e) A) * M *
          (select (n := o) q * extend (e := e) A).conjTranspose := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by simp only [select_extend, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp only [h, Matrix.mul_sum, Matrix.sum_mul]

omit [DecidableEq n] [DecidableEq e] [Fintype n] in
theorem trace_environment_sum [Fintype κ] (M : κ → Matrix (n × e) (n × e) ℂ) :
    traceEnvironment (∑ k, M k) = ∑ k, traceEnvironment (M k) := by
  ext i j : 2
  simp only [traceEnvironment, Matrix.of_apply, Matrix.sum_apply]
  exact Finset.sum_comm

omit [DecidableEq n] [DecidableEq e] [Fintype n] in
theorem trace_environment_smul (c : ℂ) (M : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment (c • M) = c • traceEnvironment M := by
  ext i j : 2
  simp [traceEnvironment, Finset.mul_sum]

/-- Any rectangular joint Kraus family, without a trace-preservation assumption. -/
theorem branch_partial_trace [Fintype κ]
    (K : κ → Matrix (o × e) (n × e) ℂ) (q : e) (M : Matrix n n ℂ) :
    traceEnvironment (∑ k, K k * prepare q M * (K k).conjTranspose) =
      ∑ kr : κ × e, (select (n := o) kr.2 * K kr.1 * insert (n := n) q) * M *
        (select (n := o) kr.2 * K kr.1 * insert (n := n) q).conjTranspose := by
  rw [trace_environment_family]
  simp only [Fintype.sum_prod_type, prepare, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  exact Finset.sum_comm

structure QuantumEnvironmentExtensionSuite : Prop where
  sandwich : ∀ (A : Matrix (Fin 4) (Fin 16) ℂ)
    (M : Matrix (Fin 16 × Fin 2) (Fin 16 × Fin 2) ℂ),
    traceEnvironment (extend A * M * (extend A).conjTranspose) =
      A * traceEnvironment M * A.conjTranspose
  branches : ∀ {κ : Type} [Fintype κ]
    (K : κ → Matrix (Fin 4 × Fin 2) (Fin 16 × Fin 2) ℂ) q M,
    traceEnvironment (∑ k, K k * prepare q M * (K k).conjTranspose) =
      ∑ kr : κ × Fin 2, (select (n := Fin 4) kr.2 * K kr.1 * insert (n := Fin 16) q) * M *
        (select (n := Fin 4) kr.2 * K kr.1 * insert (n := Fin 16) q).conjTranspose

theorem verification_suite : QuantumEnvironmentExtensionSuite :=
  ⟨trace_environment_sandwich, branch_partial_trace⟩

end QuantumEnvironmentExtension

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumOrderedNoiseComposition

/-! A finite environment retained throughout a joint circuit. Preparation and
partial trace are explicit matrices; the resulting system channel is CPTP for a
fixed initial environment basis state. Resetting after each stage is a distinct model. -/
noncomputable section
namespace QuantumPersistentEnvironment
open QuantumGateNoiseComposition QuantumNoiseTransport QuantumOrderedNoiseComposition
open scoped BigOperators ComplexOrder Matrix

variable {n e κ : Type} [Fintype n] [DecidableEq n] [Fintype e] [DecidableEq e] [Fintype κ]

/-- Isometry |i> ↦ |i,q>. -/
def insert (q : e) : Matrix (n × e) n ℂ :=
  Matrix.of fun a i => if a.1 = i ∧ a.2 = q then 1 else 0

def select (q : e) : Matrix n (n × e) ℂ := (insert (n := n) q).conjTranspose

theorem insert_isometry (q : e) : (insert (n := n) q).conjTranspose * insert (n := n) q = 1 := by
  ext i j : 2
  simp [insert, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ite_and, mul_ite, eq_comm, Matrix.one_apply]

theorem selectors_complete :
    (∑ q : e, (select (n := n) q).conjTranspose * select q) = 1 := by
  ext i j : 2
  simp [select, insert, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ite_and, ite_mul, eq_comm, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

def traceEnvironment (M : Matrix (n × e) (n × e) ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => ∑ q, M (i,q) (j,q)

theorem selector_sandwich (q : e) (M : Matrix (n × e) (n × e) ℂ) (i j : n) :
    (select (n := n) q * M * (select (n := n) q).conjTranspose) i j = M (i,q) (j,q) := by
  simp [select, insert, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, ite_and, apply_ite, eq_comm]

theorem trace_environment_family (M : Matrix (n × e) (n × e) ℂ) :
    traceEnvironment M = ∑ q : e, select q * M * (select q).conjTranspose := by
  ext i j : 2
  simp only [traceEnvironment, Matrix.of_apply, Matrix.sum_apply, selector_sandwich]

omit [DecidableEq n] [DecidableEq e] in
theorem trace_environment_trace (M : Matrix (n × e) (n × e) ℂ) :
    (traceEnvironment M).trace = M.trace := by
  simp [traceEnvironment, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

omit [Fintype n] [DecidableEq n] [DecidableEq e] in
theorem trace_environment_positive [Finite n] (M : Matrix (n × e) (n × e) ℂ) (hM : M.PosSemidef) :
    (traceEnvironment M).PosSemidef := by
  classical
  let := Fintype.ofFinite n
  rw [trace_environment_family]
  exact Matrix.posSemidef_sum _ fun q _ => hM.mul_mul_conjTranspose_same (select q)

def prepare (q : e) (M : Matrix n n ℂ) : Matrix (n × e) (n × e) ℂ :=
  insert (n := n) q * M * (insert (n := n) q).conjTranspose

omit [Fintype e] in
theorem prepare_entry (q : e) (M : Matrix n n ℂ) (a b : n × e) :
    prepare q M a b = if a.2 = q ∧ b.2 = q then M a.1 b.1 else 0 := by
  simp [prepare, insert, Matrix.mul_apply, Matrix.conjTranspose_apply,
    ite_and, ite_mul, eq_comm]
  split_ifs <;> simp_all

theorem trace_environment_prepare (q : e) (M : Matrix n n ℂ) :
    traceEnvironment (prepare q M) = M := by
  ext i j : 2
  simp [traceEnvironment, prepare_entry]

omit [Fintype e] in
theorem prepare_positive [Finite e] (q : e) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    (prepare q M).PosSemidef := hM.mul_mul_conjTranspose_same (insert (n := n) q)

theorem prepare_trace (q : e) (M : Matrix n n ℂ) : (prepare q M).trace = M.trace := by
  rw [← trace_environment_trace, trace_environment_prepare]

/-- Reduced system Kraus operator: initialize q, evolve jointly, select final environment r. -/
def reduced (E : CPTP (n × e) κ) (q : e) : CPTP n (κ × e) where
  op kr := select (n := n) kr.2 * E.op kr.1 * insert (n := n) q
  complete := by
    simp only [Fintype.sum_prod_type, Matrix.conjTranspose_mul]
    calc
      _ = ∑ k : κ, (insert (n := n) q).conjTranspose * (E.op k).conjTranspose *
          (∑ r : e, (select (n := n) r).conjTranspose * select (n := n) r) * E.op k *
          insert (n := n) q := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = (insert (n := n) q).conjTranspose * (∑ k, (E.op k).conjTranspose * E.op k) *
          insert (n := n) q := by
        simp only [selectors_complete, Matrix.mul_one, Matrix.mul_sum, Matrix.sum_mul,
          Matrix.mul_assoc]
      _ = 1 := by rw [E.complete, Matrix.mul_one, insert_isometry]

theorem reduced_map (E : CPTP (n × e) κ) (q : e) (M : Matrix n n ℂ) :
    (reduced E q).map M = traceEnvironment (E.map (prepare q M)) := by
  rw [trace_environment_family]
  simp only [CPTP.map, reduced, prepare, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  exact Finset.sum_comm

/-- The environment is initialized once and is not erased between stages. -/
def persistent (ss : List (Stage (n × e))) (q : e) : CPTP n (Paths ss × e) :=
  reduced (direct ss) q

theorem persistent_map (ss : List (Stage (n × e))) (q : e) (M : Matrix n n ℂ) :
    (persistent ss q).map M = traceEnvironment (run ss (prepare q M)) := by
  rw [persistent, reduced_map, direct_map_run]

/-- Reset model: retain the system marginal, replace its environment with |q> after each stage. -/
def resetStage (q : e) (s : Stage (n × e)) : Stage n :=
  ⟨s.labels × e, inferInstance, identityGate n, reduced (noisyGate s.gate s.noise) q⟩

def resetRun (ss : List (Stage (n × e))) (q : e) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  run (ss.map (resetStage q)) M

theorem reset_run_nil (q : e) (M : Matrix n n ℂ) : resetRun [] q M = M := rfl

theorem reset_run_cons (s : Stage (n × e)) (ss : List (Stage (n × e))) (q : e)
    (M : Matrix n n ℂ) : resetRun (s :: ss) q M =
      resetRun ss q ((reduced (noisyGate s.gate s.noise) q).map M) := by
  simp only [resetRun, List.map_cons, run, resetStage, identityGate,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/-- Sufficient refresh condition: no system-environment correlation remains and |q> returns. -/
def ReturnsFresh (q : e) (s : Stage (n × e)) : Prop :=
  ∀ M : Matrix n n ℂ, (noisyGate s.gate s.noise).map (prepare q M) =
    prepare q ((reduced (noisyGate s.gate s.noise) q).map M)

theorem joint_run_fresh (ss : List (Stage (n × e))) (q : e)
    (h : ∀ s ∈ ss, ReturnsFresh q s) (M : Matrix n n ℂ) :
    run ss (prepare q M) = prepare q (resetRun ss q M) := by
  induction ss generalizing M with
  | nil => rfl
  | cons s ss ih =>
    change run ss (s.noise.map (s.gate.matrix * prepare q M * s.gate.matrix.conjTranspose)) = _
    rw [← noisy_gate_map, h s (by simp), ih (fun t ht => h t (by simp [ht]))]
    rw [reset_run_cons]

theorem persistent_equals_reset_of_fresh (ss : List (Stage (n × e))) (q : e)
    (h : ∀ s ∈ ss, ReturnsFresh q s) (M : Matrix n n ℂ) :
    (persistent ss q).map M = resetRun ss q M := by
  rw [persistent_map, joint_run_fresh ss q h, trace_environment_prepare]

structure QuantumPersistentEnvironmentSuite : Prop where
  reduced_semantics : ∀ {κ : Type} [Fintype κ]
    (E : CPTP (Fin 16 × Fin 2) κ) q M,
    (reduced E q).map M = traceEnvironment (E.map (prepare q M))
  persistent_semantics : ∀ (ss : List (Stage (Fin 16 × Fin 2))) q M,
    (persistent ss q).map M = traceEnvironment (run ss (prepare q M))
  refresh : ∀ (ss : List (Stage (Fin 16 × Fin 2))) q,
    (∀ s ∈ ss, ReturnsFresh q s) → ∀ M, (persistent ss q).map M = resetRun ss q M

theorem verification_suite : QuantumPersistentEnvironmentSuite :=
  ⟨reduced_map, persistent_map, persistent_equals_reset_of_fresh⟩

end QuantumPersistentEnvironment

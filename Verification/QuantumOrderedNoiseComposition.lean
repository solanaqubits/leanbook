/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoiseTransport

/-! Ordered finite noisy circuits. Every stage has its own finite Kraus index.
The direct path operator and the accumulated input-noise operator are defined
separately and related by a matrix factorization theorem. -/
noncomputable section
namespace QuantumOrderedNoiseComposition
open QuantumGateNoiseComposition QuantumNoiseTransport
open scoped BigOperators ComplexOrder Matrix

variable {n κ ι : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [Fintype ι]

/-- E acts first, then F. The pair of labels is in chronological order. -/
def compose (F : CPTP n ι) (E : CPTP n κ) : CPTP n (κ × ι) where
  op kj := F.op kj.2 * E.op kj.1
  complete := by
    simp only [Matrix.conjTranspose_mul, Fintype.sum_prod_type]
    have hk (k : κ) : ∑ j, (E.op k).conjTranspose * (F.op j).conjTranspose *
        (F.op j * E.op k) = (E.op k).conjTranspose * E.op k := by
      calc
        _ = (E.op k).conjTranspose * (∑ j, (F.op j).conjTranspose * F.op j) * E.op k := by
          simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        _ = _ := by rw [F.complete, Matrix.mul_one]
    simp only [hk, E.complete]

theorem compose_map (F : CPTP n ι) (E : CPTP n κ) (M : Matrix n n ℂ) :
    (compose F E).map M = F.map (E.map M) := by
  simp only [CPTP.map, compose, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  exact Finset.sum_comm

/-- V follows U. -/
def gateCompose (V U : UnitaryGate n) : UnitaryGate n where
  matrix := V.matrix * U.matrix
  left := by
    simp only [Matrix.conjTranspose_mul]
    calc
      _ = U.matrix.conjTranspose * (V.matrix.conjTranspose * V.matrix) * U.matrix := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [V.left, Matrix.mul_one, U.left]
  right := by
    simp only [Matrix.conjTranspose_mul]
    calc
      _ = V.matrix * (U.matrix * U.matrix.conjTranspose) * V.matrix.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [U.right, Matrix.mul_one, V.right]

def identityGate (n : Type*) [Fintype n] [DecidableEq n] : UnitaryGate n :=
  ⟨1, by simp, by simp⟩

/-- An ideal gate followed immediately by its noise, retaining only the noise label. -/
def noisyGate (U : UnitaryGate n) (E : CPTP n κ) : CPTP n κ where
  op k := E.op k * U.matrix
  complete := by
    simp only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
    have hk (k : κ) : U.matrix.conjTranspose * (E.op k).conjTranspose * E.op k * U.matrix =
        U.matrix.conjTranspose * ((E.op k).conjTranspose * E.op k) * U.matrix := by
      simp only [Matrix.mul_assoc]
    simp only [hk, ← Matrix.mul_sum, ← Matrix.sum_mul, E.complete, Matrix.mul_one, U.left]

theorem noisy_gate_map (U : UnitaryGate n) (E : CPTP n κ) (M : Matrix n n ℂ) :
    (noisyGate U E).map M = E.map (U.matrix * M * U.matrix.conjTranspose) := by
  simp only [CPTP.map, noisyGate, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem pullback_compose_map (U : UnitaryGate n) (F : CPTP n ι) (E : CPTP n κ)
    (M : Matrix n n ℂ) :
    (pullback U (compose F E)).map M = (pullback U F).map ((pullback U E).map M) := by
  rw [pullback_map, compose_map, pullback_map, ← slide_channel]

theorem nested_pullback_map (U V : UnitaryGate n) (E : CPTP n κ) (M : Matrix n n ℂ) :
    (pullback U (pullback V E)).map M = (pullback (gateCompose V U) E).map M := by
  simp only [pullback_map, gateCompose, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Finite channels may have different numbers and types of Kraus labels at each stage. -/
structure Stage (n : Type*) [Fintype n] [DecidableEq n] where
  labels : Type
  finiteLabels : Fintype labels
  gate : UnitaryGate n
  noise : @CPTP n labels _ _ finiteLabels

attribute [instance] Stage.finiteLabels

@[reducible] def Paths : List (Stage n) → Type
  | [] => Unit
  | s :: ss => s.labels × Paths ss

@[reducible] instance pathsFintype : (ss : List (Stage n)) → Fintype (Paths ss)
  | [] => inferInstanceAs (Fintype Unit)
  | s :: ss => @instFintypeProd s.labels (Paths ss) s.finiteLabels (pathsFintype ss)

/-- Direct noisy circuit Kraus operators, with the first list element acting first. -/
def direct : (ss : List (Stage n)) → CPTP n (Paths ss)
  | [] => identityChannel n
  | s :: ss => compose (direct ss) (noisyGate s.gate s.noise)

def ideal : List (Stage n) → UnitaryGate n
  | [] => identityGate n
  | s :: ss => gateCompose (ideal ss) s.gate

/-- Accumulated input noise: the tail's effective error follows the first error,
then that ordered composition is pulled back through the first ideal gate. -/
def effective : (ss : List (Stage n)) → CPTP n (Paths ss)
  | [] => identityChannel n
  | s :: ss => pullback s.gate (compose (effective ss) s.noise)

/-- Independently specified chronological state evolution. -/
def run : List (Stage n) → Matrix n n ℂ → Matrix n n ℂ
  | [], M => M
  | s :: ss, M => run ss (s.noise.map (s.gate.matrix * M * s.gate.matrix.conjTranspose))

theorem direct_map_run (ss : List (Stage n)) (M : Matrix n n ℂ) :
    (direct ss).map M = run ss M := by
  induction ss generalizing M with
  | nil => exact identity_map M
  | cons s ss ih =>
    change (compose (direct ss) (noisyGate s.gate s.noise)).map M = _
    rw [compose_map, noisy_gate_map, ih, run]

theorem run_append (ss tt : List (Stage n)) (M : Matrix n n ℂ) :
    run (ss ++ tt) M = run tt (run ss M) := by
  induction ss generalizing M with
  | nil => rfl
  | cons s ss ih => exact ih _

/-- Full pathwise matrix equality; no input ensemble or positivity assumptions. -/
theorem path_factorization (ss : List (Stage n)) (path : Paths ss) :
    (direct ss).op path = (ideal ss).matrix * (effective ss).op path := by
  induction ss with
  | nil => simp [direct, ideal, effective, identityGate, identityChannel]
  | cons s ss ih =>
    rcases path with ⟨k,ks⟩
    change (direct ss).op ks * (s.noise.op k * s.gate.matrix) =
      ((ideal ss).matrix * s.gate.matrix) *
        (pullback s.gate (compose (effective ss) s.noise)).op (k,ks)
    rw [ih ks]
    have h := slide_branch s.gate (compose (effective ss) s.noise) (ideal ss).matrix (k,ks)
    simpa only [compose, Matrix.mul_assoc] using h

theorem circuit_factorization (ss : List (Stage n)) (M : Matrix n n ℂ) :
    (direct ss).map M = (ideal ss).matrix * (effective ss).map M *
      (ideal ss).matrix.conjTranspose := by
  simp only [CPTP.map, path_factorization, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem run_effective (ss : List (Stage n)) (M : Matrix n n ℂ) :
    run ss M = (ideal ss).matrix * (effective ss).map M *
      (ideal ss).matrix.conjTranspose := by
  rw [← direct_map_run, circuit_factorization]

theorem run_trace (ss : List (Stage n)) (M : Matrix n n ℂ) : (run ss M).trace = M.trace := by
  rw [← direct_map_run, CPTP.trace]

theorem run_positive (ss : List (Stage n)) (M : Matrix n n ℂ) (hM : M.PosSemidef) :
    (run ss M).PosSemidef := by
  rw [← direct_map_run]
  exact (direct ss).positive M hM

theorem singleton_effective (s : Stage n) (M : Matrix n n ℂ) :
    (effective [s]).map M = (pullback s.gate s.noise).map M := by
  change (pullback s.gate (compose (identityChannel n) s.noise)).map M = _
  rw [pullback_map, compose_map, identity_map, pullback_map]

/-- Chronological two-error formula: later error is conjugated by the full ideal prefix. -/
theorem two_stage_effective (s t : Stage n) (M : Matrix n n ℂ) :
    (effective [s,t]).map M =
      (pullback (gateCompose t.gate s.gate) t.noise).map
        ((pullback s.gate s.noise).map M) := by
  change (pullback s.gate (compose (effective [t]) s.noise)).map M = _
  rw [pullback_compose_map, pullback_map, singleton_effective, ← pullback_map,
    nested_pullback_map]

structure QuantumOrderedNoiseCompositionSuite : Prop where
  paths : ∀ (ss : List (Stage (Fin 16))) path,
    (direct ss).op path = (ideal ss).matrix * (effective ss).op path
  evolution : ∀ (ss : List (Stage (Fin 16))) M,
    run ss M = (ideal ss).matrix * (effective ss).map M * (ideal ss).matrix.conjTranspose
  concatenation : ∀ (ss tt : List (Stage (Fin 16))) M,
    run (ss ++ tt) M = run tt (run ss M)

theorem verification_suite : QuantumOrderedNoiseCompositionSuite :=
  ⟨path_factorization, run_effective, run_append⟩

end QuantumOrderedNoiseComposition

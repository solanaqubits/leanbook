/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumEnvironmentExtension

/-! A binary environment controlled by a system basis label. Two coherent
couplings cancel, whereas discarding the environment removes inter-label coherence. -/
noncomputable section
namespace QuantumBinaryMemoryCoupling
open QuantumGateNoiseComposition QuantumNoiseTransport QuantumOrderedNoiseComposition
open QuantumPersistentEnvironment QuantumEnvironmentExtension
open scoped BigOperators ComplexOrder Matrix

variable {n : Type}

def flipIndex (f : n → Bool) (a : n × Bool) : n × Bool := (a.1, xor a.2 (f a.1))

theorem flip_involutive (f : n → Bool) (a : n × Bool) : flipIndex f (flipIndex f a) = a := by
  rcases a with ⟨i,b⟩
  cases b <;> cases h : f i <;> simp [flipIndex, h]

theorem flip_eq_iff (f : n → Bool) (a b : n × Bool) :
    flipIndex f a = b ↔ a = flipIndex f b := by
  constructor
  · intro h; rw [← h, flip_involutive]
  · intro h; rw [h, flip_involutive]

variable [Fintype n] [DecidableEq n]

def couplingMatrix (f : n → Bool) : Matrix (n × Bool) (n × Bool) ℂ :=
  Matrix.of fun a b => if flipIndex f a = b then 1 else 0

theorem coupling_left (f : n → Bool) (M : Matrix (n × Bool) (n × Bool) ℂ) (a b) :
    (couplingMatrix f * M) a b = M (flipIndex f a) b := by
  simp [couplingMatrix, Matrix.mul_apply]

theorem coupling_right (f : n → Bool) (M : Matrix (n × Bool) (n × Bool) ℂ) (a b) :
    (M * couplingMatrix f) a b = M a (flipIndex f b) := by
  simp [couplingMatrix, Matrix.mul_apply, flip_eq_iff]

omit [Fintype n] in
theorem coupling_adjoint (f : n → Bool) : (couplingMatrix f).conjTranspose = couplingMatrix f := by
  ext a b : 2
  have h : flipIndex f b = a ↔ flipIndex f a = b := by
    rw [flip_eq_iff f b a]
    exact eq_comm
  simp only [couplingMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, h]
  split_ifs <;> simp

theorem coupling_squared (f : n → Bool) : couplingMatrix f * couplingMatrix f = 1 := by
  ext a b : 2
  rw [coupling_left]
  simp [couplingMatrix, flip_involutive, Matrix.one_apply]

def coupling (f : n → Bool) : UnitaryGate (n × Bool) :=
  ⟨couplingMatrix f, by rw [coupling_adjoint, coupling_squared],
    by rw [coupling_adjoint, coupling_squared]⟩

theorem coupling_map_entry (f : n → Bool) (M : Matrix (n × Bool) (n × Bool) ℂ) (a b) :
    (coupling f).channel.map M a b = M (flipIndex f a) (flipIndex f b) := by
  rw [unitary_channel_map]
  change (couplingMatrix f * M * (couplingMatrix f).conjTranspose) a b = _
  rw [coupling_adjoint, coupling_right, coupling_left]

def dephase (f : n → Bool) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => if f i = f j then M i j else 0

theorem reduced_coupling (f : n → Bool) (M : Matrix n n ℂ) :
    (reduced (coupling f).channel false).map M = dephase f M := by
  rw [reduced_map]
  ext i j : 2
  cases hi : f i <;> cases hj : f j <;>
    simp [traceEnvironment, coupling_map_entry, flipIndex, prepare_entry, dephase, hi, hj]

omit [Fintype n] [DecidableEq n] in
theorem dephase_idempotent (f : n → Bool) (M : Matrix n n ℂ) :
    dephase f (dephase f M) = dephase f M := by
  ext i j : 2
  by_cases h : f i = f j <;> simp [dephase, h]

/-- A gate with no matrix elements between flag sectors commutes with the coupling. -/
theorem coupling_commutes (f : n → Bool) (A : Matrix n n ℂ)
    (hA : ∀ i j, f i ≠ f j → A i j = 0) :
    couplingMatrix f * extend A = extend A * couplingMatrix f := by
  ext a b : 2
  rw [coupling_left, coupling_right]
  by_cases h : f a.1 = f b.1
  · rcases a with ⟨i,u⟩; rcases b with ⟨j,v⟩
    cases u <;> cases v <;> cases hi : f i <;> cases hj : f j <;>
      simp_all [extend, flipIndex]
  · simp [extend, flipIndex, hA _ _ h]

theorem coupling_twice (f : n → Bool) (M : Matrix (n × Bool) (n × Bool) ℂ) :
    (coupling f).channel.map ((coupling f).channel.map M) = M := by
  ext a b : 2
  rw [coupling_map_entry, coupling_map_entry, flip_involutive, flip_involutive]

theorem extend_prepare (A : Matrix n n ℂ) (q : Bool) (M : Matrix n n ℂ) :
    extend A * prepare q M * (extend A).conjTranspose =
      prepare q (A * M * A.conjTranspose) := by
  calc
    extend (e := Bool) A * prepare q M * (extend (e := Bool) A).conjTranspose =
        (extend (e := Bool) A * insert (n := n) q) * M *
        (extend (e := Bool) A * insert (n := n) q).conjTranspose := by
      simp only [prepare, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by simp only [extend_insert, prepare, Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem commuting_sandwich (C A M : Matrix n n ℂ) (h : C * A = A * C) :
    C * (A * M * A.conjTranspose) * C.conjTranspose =
      A * (C * M * C.conjTranspose) * A.conjTranspose := by
  calc
    _ = (C * A) * M * (C * A).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem dephase_sandwich (f : n → Bool) (A M : Matrix n n ℂ)
    (hA : ∀ i j, f i ≠ f j → A i j = 0) :
    dephase f (A * M * A.conjTranspose) = A * dephase f M * A.conjTranspose := by
  classical
  rw [← reduced_coupling, reduced_map, unitary_channel_map, ← extend_prepare]
  change traceEnvironment (couplingMatrix f *
    (extend A * prepare false M * (extend A).conjTranspose) *
    (couplingMatrix f).conjTranspose) = _
  rw [commuting_sandwich _ _ _ (coupling_commutes f A hA), trace_environment_sandwich]
  change A * traceEnvironment ((coupling f).matrix * prepare false M *
    (coupling f).matrix.conjTranspose) * A.conjTranspose = _
  rw [← unitary_channel_map]
  rw [← reduced_map, reduced_coupling]

theorem reduced_noisy_coupling (f : n → Bool) (U : UnitaryGate n) (M : Matrix n n ℂ) :
    (reduced (noisyGate (extendGate U) (coupling f).channel) false).map M =
      dephase f (U.matrix * M * U.matrix.conjTranspose) := by
  rw [reduced_map, noisy_gate_map]
  change traceEnvironment ((coupling f).channel.map
    (extend U.matrix * prepare false M * (extend U.matrix).conjTranspose)) = _
  rw [extend_prepare, ← reduced_map, reduced_coupling]

theorem pullback_coupling (f : n → Bool) (U : UnitaryGate n)
    (hU : ∀ i j, f i ≠ f j → U.matrix i j = 0)
    (M : Matrix (n × Bool) (n × Bool) ℂ) :
    (pullback (extendGate U) (coupling f).channel).map M = (coupling f).channel.map M := by
  have hop : (extend U.matrix).conjTranspose * couplingMatrix f * extend U.matrix =
      couplingMatrix f := by
    rw [Matrix.mul_assoc, coupling_commutes f U.matrix hU, ← Matrix.mul_assoc]
    rw [extend_adjoint, extend_mul, U.left, extend_one, Matrix.one_mul]
  simp only [CPTP.map, pullback, extendGate, UnitaryGate.channel, coupling, hop]

structure QuantumBinaryMemoryCouplingSuite : Prop where
  involution : ∀ (f : Fin 16 → Bool), couplingMatrix f * couplingMatrix f = 1
  reduction : ∀ (f : Fin 16 → Bool) M,
    (reduced (coupling f).channel false).map M = dephase f M
  commuting : ∀ (f : Fin 16 → Bool) A,
    (∀ i j, f i ≠ f j → A i j = 0) → couplingMatrix f * extend A = extend A * couplingMatrix f

theorem verification_suite : QuantumBinaryMemoryCouplingSuite :=
  ⟨coupling_squared, reduced_coupling, coupling_commutes⟩

end QuantumBinaryMemoryCoupling

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPersistentEnvironment
import Verification.QuantumInternalBSMNoise

/-! A retained one-qubit memory restores coherence after two CNOT collisions.
Fresh-environment composition dephases instead. No map of the first system
marginal alone can reproduce both final coherent states. -/
noncomputable section
namespace QuantumMemoryCounterexample
open QuantumPauliDensityBridge QuantumEntanglementSwappingPurificationContract
open QuantumStateAvailabilityContract QuantumBellCircuitRefinement
open QuantumGateNoiseComposition QuantumNoiseTransport QuantumInternalBSMNoise
open QuantumOrderedNoiseComposition QuantumPersistentEnvironment
open scoped BigOperators ComplexOrder Matrix

abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ

/-- System is control, retained environment is target. -/
def collision : Stage PairIndex :=
  ⟨Unit, inferInstance, cnotGate, identityChannel PairIndex⟩

theorem run_one_collision (M : PairDensity) :
    run [collision] M = cnotGate.channel.map M := by
  change (identityChannel PairIndex).map
    (cnotGate.matrix * M * cnotGate.matrix.conjTranspose) = cnotGate.channel.map M
  rw [identity_map, unitary_channel_map]

theorem cnot_twice (M : PairDensity) :
    cnotGate.channel.map (cnotGate.channel.map M) = M := by
  rw [unitary_channel_map, unitary_channel_map]
  change cnot * (cnot * M * cnot.conjTranspose) * cnot.conjTranspose = M
  rw [cnot_adjoint]
  calc
    _ = (cnot * cnot) * M * (cnot * cnot) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [cnot_squared]; simp

theorem run_two_collisions (M : PairDensity) : run [collision,collision] M = M := by
  have h : [collision,collision] = [collision] ++ [collision] := rfl
  rw [h, run_append, run_one_collision, run_one_collision, cnot_twice]

def dephase (M : Qubit) : Qubit := Matrix.diagonal M.diag

theorem collision_reduced_map (M : Qubit) :
    (reduced cnotGate.channel (0 : Fin 2)).map M = dephase M := by
  rw [reduced_map, unitary_channel_map]
  ext a b : 2
  fin_cases a <;> fin_cases b <;>
    simp [traceEnvironment, cnotGate, cnot, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, prepare_entry, dephase, Matrix.diag]

theorem persistent_once (M : Qubit) :
    (persistent [collision] (0 : Fin 2)).map M = dephase M := by
  rw [persistent_map, run_one_collision, ← reduced_map, collision_reduced_map]

theorem persistent_twice (M : Qubit) :
    (persistent [collision,collision] (0 : Fin 2)).map M = M := by
  rw [persistent_map, run_two_collisions, trace_environment_prepare]

theorem reset_collision_map (M : Qubit) :
    (reduced (noisyGate collision.gate collision.noise) (0 : Fin 2)).map M = dephase M := by
  rw [reduced_map, noisy_gate_map]
  change traceEnvironment ((identityChannel PairIndex).map
    (cnotGate.matrix * prepare (0 : Fin 2) M * cnotGate.matrix.conjTranspose)) = _
  rw [identity_map, ← unitary_channel_map, ← reduced_map, collision_reduced_map]

theorem dephase_idempotent (M : Qubit) : dephase (dephase M) = dephase M := by
  simp [dephase]

theorem reset_twice (M : Qubit) : resetRun [collision,collision] (0 : Fin 2) M = dephase M := by
  rw [reset_run_cons, reset_collision_map, reset_run_cons, reset_collision_map,
    reset_run_nil, dephase_idempotent]

/-- |+> and |->, with exact normalization from the shared Bell coefficient. -/
def amplitude (minus : Bool) (i : Fin 2) : ℂ :=
  if minus = true ∧ i = 1 then -bellCoeff else bellCoeff

def coherent (minus : Bool) : Qubit :=
  Matrix.vecMulVec (amplitude minus) (star (amplitude minus))

theorem coherent_positive (minus : Bool) : (coherent minus).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem coherent_trace (minus : Bool) : (coherent minus).trace = 1 := by
  cases minus <;> norm_num [coherent, amplitude, Matrix.trace, Matrix.diag,
    Matrix.vecMulVec, Fin.sum_univ_two, ← pow_two, bellCoeff_sq]

theorem coherent_offdiagonal (minus : Bool) :
    coherent minus 0 1 = if minus then -(1/2 : ℂ) else 1/2 := by
  cases minus <;> norm_num [coherent, amplitude, Matrix.vecMulVec, ← pow_two, bellCoeff_sq]

theorem dephase_coherent (minus : Bool) : dephase (coherent minus) = (1/2 : ℂ) • (1 : Qubit) := by
  ext i j : 2
  cases minus <;> fin_cases i <;> fin_cases j <;>
    norm_num [dephase, coherent, amplitude, Matrix.diag, Matrix.vecMulVec,
      ← pow_two, bellCoeff_sq]

theorem coherent_states_distinct : coherent false ≠ coherent true := by
  intro h
  have he := congrArg (fun M : Qubit => M 0 1) h
  rw [coherent_offdiagonal, coherent_offdiagonal] at he
  norm_num at he

/-- The first marginal loses the phase label, although the joint register retains it. -/
theorem first_marginals_equal :
    (persistent [collision] (0 : Fin 2)).map (coherent false) =
      (persistent [collision] (0 : Fin 2)).map (coherent true) := by
  rw [persistent_once, persistent_once, dephase_coherent, dephase_coherent]

theorem retained_and_reset_differ :
    (persistent [collision,collision] (0 : Fin 2)).map (coherent false) 0 1 = 1/2 ∧
    resetRun [collision,collision] (0 : Fin 2) (coherent false) 0 1 = 0 := by
  rw [persistent_twice, reset_twice, coherent_offdiagonal, dephase_coherent]
  norm_num

/-- Not even an arbitrary deterministic function of the first reduced state can
recover both final states; this is stronger than exclusion of a CPTP intermediate map. -/
theorem no_system_only_intermediate_map :
    ¬ ∃ f : Qubit → Qubit, ∀ M : Qubit, M.PosSemidef → M.trace = 1 →
      f ((persistent [collision] (0 : Fin 2)).map M) =
        (persistent [collision,collision] (0 : Fin 2)).map M := by
  rintro ⟨f,hf⟩
  have hp := hf (coherent false) (coherent_positive false) (coherent_trace false)
  have hm := hf (coherent true) (coherent_positive true) (coherent_trace true)
  rw [persistent_twice] at hp hm
  rw [first_marginals_equal] at hp
  exact coherent_states_distinct (hp.symm.trans hm)

/-- The sufficient refresh hypothesis fails at the first entangling collision. -/
theorem collision_not_fresh : ¬ ReturnsFresh (0 : Fin 2) collision := by
  intro h
  have he := persistent_equals_reset_of_fresh [collision,collision] (0 : Fin 2)
    (by intro s hs; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hs
        subst s; exact h) (coherent false)
  have entry := congrArg (fun M : Qubit => M 0 1) he
  rw [retained_and_reset_differ.1, retained_and_reset_differ.2] at entry
  norm_num at entry

structure QuantumMemoryCounterexampleSuite : Prop where
  coherent_recovery : ∀ M : Qubit, (persistent [collision,collision] (0 : Fin 2)).map M = M
  fresh_dephasing : ∀ M : Qubit, resetRun [collision,collision] (0 : Fin 2) M = dephase M
  information_loss : ¬ ∃ f : Qubit → Qubit, ∀ M : Qubit, M.PosSemidef → M.trace = 1 →
    f ((persistent [collision] (0 : Fin 2)).map M) =
      (persistent [collision,collision] (0 : Fin 2)).map M

theorem verification_suite : QuantumMemoryCounterexampleSuite :=
  ⟨persistent_twice, reset_twice, no_system_only_intermediate_map⟩

end QuantumMemoryCounterexample

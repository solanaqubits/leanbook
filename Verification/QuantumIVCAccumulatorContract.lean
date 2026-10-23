/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Boolean accumulation and a clipped scalar loss ledger

Validity flags and declared losses are inputs, not authenticated proofs or quantum states.
Step indices are deliberately not checked. Semantic soundness needs an external premise.
The verifier expression counts symbolic unit-cost primitives; it does not establish
rational bit complexity, compiled Lean running time or hardware constant time.
-/
namespace QuantumIVCAccumulatorContract

structure StepWitness where
  stepIndex : ℕ
  valid : Bool
  fidelityLoss : ℚ
  h_loss_nonneg : 0 ≤ fidelityLoss

@[ext] structure IVCAccumulator where
  totalSteps : ℕ
  allValid : Bool
  accumulatedFidelity : ℚ
  h_fid_nonneg : 0 ≤ accumulatedFidelity
  h_fid_le_one : accumulatedFidelity ≤ 1

def emptyAccumulator : IVCAccumulator := ⟨0, true, 1, by norm_num, by norm_num⟩

def foldStep (acc : IVCAccumulator) (w : StepWitness) : IVCAccumulator where
  totalSteps := acc.totalSteps + 1
  allValid := acc.allValid && w.valid
  accumulatedFidelity := max 0 (acc.accumulatedFidelity - w.fidelityLoss)
  h_fid_nonneg := le_max_left _ _
  h_fid_le_one := max_le (by norm_num)
    (by linarith [acc.h_fid_le_one, w.h_loss_nonneg])

def foldSteps (acc : IVCAccumulator) : List StepWitness → IVCAccumulator
  | [] => acc
  | w :: ws => foldSteps (foldStep acc w) ws

def verifyAccumulator (acc : IVCAccumulator) (Fmin : ℚ) : Bool :=
  acc.allValid && decide (Fmin ≤ acc.accumulatedFidelity)

theorem fold_fidelity_bounds (acc : IVCAccumulator) (w : StepWitness) :
    0 ≤ (foldStep acc w).accumulatedFidelity ∧
      (foldStep acc w).accumulatedFidelity ≤ 1 :=
  ⟨(foldStep acc w).h_fid_nonneg, (foldStep acc w).h_fid_le_one⟩

theorem history_fidelity_bounds (acc : IVCAccumulator) (ws : List StepWitness) :
    0 ≤ (foldSteps acc ws).accumulatedFidelity ∧
      (foldSteps acc ws).accumulatedFidelity ≤ 1 :=
  ⟨(foldSteps acc ws).h_fid_nonneg, (foldSteps acc ws).h_fid_le_one⟩

theorem accumulator_bounds_invariant (acc : IVCAccumulator) (w : StepWitness) :
    0 ≤ (foldStep acc w).accumulatedFidelity ∧
      (foldStep acc w).accumulatedFidelity ≤ 1 := fold_fidelity_bounds acc w

theorem fold_fidelity_nonincreasing (acc : IVCAccumulator) (w : StepWitness) :
    (foldStep acc w).accumulatedFidelity ≤ acc.accumulatedFidelity :=
  max_le acc.h_fid_nonneg (sub_le_self _ w.h_loss_nonneg)

theorem fold_soundness_preservation (acc : IVCAccumulator) (w : StepWitness)
    (ha : acc.allValid = true) (hw : w.valid = true) : (foldStep acc w).allValid = true := by
  simp [foldStep, ha, hw]

theorem folding_soundness_preservation (acc : IVCAccumulator) (w : StepWitness)
    (ha : acc.allValid = true) (hw : w.valid = true) : (foldStep acc w).allValid = true :=
  fold_soundness_preservation acc w ha hw

theorem count_after_fold (acc : IVCAccumulator) (ws : List StepWitness) :
    (foldSteps acc ws).totalSteps = acc.totalSteps + ws.length := by
  induction ws generalizing acc with
  | nil => simp [foldSteps]
  | cons w ws ih => simp [foldSteps, ih, foldStep, Nat.add_comm, Nat.add_left_comm]

theorem all_valid_iff (acc : IVCAccumulator) (ws : List StepWitness) :
    (foldSteps acc ws).allValid = true ↔ acc.allValid = true ∧ ∀ w ∈ ws, w.valid = true := by
  induction ws generalizing acc with
  | nil => simp [foldSteps]
  | cons w ws ih => simp [foldSteps, ih, foldStep, and_assoc]

theorem falsity_absorption (acc : IVCAccumulator) (ws : List StepWitness)
    (ha : acc.allValid = false) : (foldSteps acc ws).allValid = false := by
  cases hb : (foldSteps acc ws).allValid with
  | false => rfl
  | true => have h := ((all_valid_iff acc ws).mp hb).1; simp [ha] at h

theorem false_witness_absorption (acc : IVCAccumulator) (ws : List StepWitness)
    (w : StepWitness) (hw : w ∈ ws) (hf : w.valid = false) :
    (foldSteps acc ws).allValid = false := by
  cases hb : (foldSteps acc ws).allValid with
  | false => rfl
  | true => have h := ((all_valid_iff acc ws).mp hb).2 w hw; simp [hf] at h

theorem folding_falsity_absorption (acc : IVCAccumulator) (w : StepWitness)
    (ws : List StepWitness) (hw : w.valid = false) :
    (foldSteps (foldStep acc w) ws).allValid = false := by
  apply falsity_absorption
  simp [foldStep, hw]

theorem foldSteps_append (acc : IVCAccumulator) (xs ys : List StepWitness) :
    foldSteps acc (xs ++ ys) = foldSteps (foldSteps acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons w ws ih => simpa [foldSteps] using ih (foldStep acc w)

theorem false_history_suffix (acc : IVCAccumulator) (xs ys : List StepWitness)
    (hx : (foldSteps acc xs).allValid = false) :
    (foldSteps acc (xs ++ ys)).allValid = false := by
  rw [foldSteps_append]
  exact falsity_absorption _ _ hx

def totalLoss : List StepWitness → ℚ
  | [] => 0
  | w :: ws => w.fidelityLoss + totalLoss ws

theorem totalLoss_nonnegative (ws : List StepWitness) : 0 ≤ totalLoss ws := by
  induction ws with
  | nil => simp [totalLoss]
  | cons w ws ih => exact add_nonneg w.h_loss_nonneg ih

theorem clipped_subtraction_comp (F a b : ℚ) (hb : 0 ≤ b) :
    max 0 (max 0 (F - a) - b) = max 0 (F - (a + b)) := by
  by_cases h : 0 ≤ F - a
  · rw [max_eq_right h]
    congr 1
    ring
  · have hfa : F - a ≤ 0 := le_of_not_ge h
    have hfab : F - (a + b) ≤ 0 := by linarith
    rw [max_eq_left hfa, max_eq_left hfab, zero_sub, max_eq_left (neg_nonpos.mpr hb)]

theorem exact_fidelity_after_fold (acc : IVCAccumulator) (ws : List StepWitness) :
    (foldSteps acc ws).accumulatedFidelity =
      max 0 (acc.accumulatedFidelity - totalLoss ws) := by
  induction ws generalizing acc with
  | nil => simp [foldSteps, totalLoss, max_eq_right acc.h_fid_nonneg]
  | cons w ws ih =>
    rw [foldSteps, ih]
    exact clipped_subtraction_comp _ _ _ (totalLoss_nonnegative ws)

theorem totalLoss_le_length_mul (ws : List StepWitness) (eps : ℚ)
    (hw : ∀ w ∈ ws, w.fidelityLoss ≤ eps) : totalLoss ws ≤ (ws.length : ℚ) * eps := by
  induction ws with
  | nil => simp [totalLoss]
  | cons w ws ih =>
    have hh := hw w (by simp)
    have ht := ih (fun v hv => hw v (by simp [hv]))
    simp only [totalLoss, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem linear_fidelity_lower_bound (acc : IVCAccumulator) (ws : List StepWitness)
    (eps : ℚ) (heps : 0 ≤ eps) (hw : ∀ w ∈ ws, w.fidelityLoss ≤ eps) :
    max 0 (acc.accumulatedFidelity - (ws.length : ℚ) * eps) ≤
      (foldSteps acc ws).accumulatedFidelity := by
  have hbudget : 0 ≤ (ws.length : ℚ) * eps := mul_nonneg (Nat.cast_nonneg _) heps
  have ht := totalLoss_le_length_mul ws eps hw
  rw [exact_fidelity_after_fold]
  exact max_le_max (le_refl 0) (by linarith)

theorem verify_accept_iff (acc : IVCAccumulator) (Fmin : ℚ) :
    verifyAccumulator acc Fmin = true ↔ acc.allValid = true ∧
      Fmin ≤ acc.accumulatedFidelity := by simp [verifyAccumulator]

/-- Boolean flags imply semantics only under the supplied external soundness premise. -/
theorem conditional_semantic_soundness (R : StepWitness → Prop) (acc : IVCAccumulator)
    (ws : List StepWitness) (Fmin : ℚ)
    (hR : ∀ w ∈ ws, w.valid = true → R w)
    (ha : verifyAccumulator (foldSteps acc ws) Fmin = true) : ∀ w ∈ ws, R w := by
  have hv := ((all_valid_iff acc ws).mp ((verify_accept_iff _ _).mp ha).1).2
  intro w hw
  exact hR w hw (hv w hw)

theorem threshold_above_one_rejected (acc : IVCAccumulator) (Fmin : ℚ) (hF : 1 < Fmin) :
    verifyAccumulator acc Fmin = false := by
  have h : ¬ Fmin ≤ acc.accumulatedFidelity := by linarith [acc.h_fid_le_one]
  simp [verifyAccumulator, h]

theorem nonpositive_threshold_acceptance (acc : IVCAccumulator) (Fmin : ℚ)
    (hF : Fmin ≤ 0) : verifyAccumulator acc Fmin = acc.allValid := by
  simp [verifyAccumulator, hF.trans acc.h_fid_nonneg]

theorem empty_acceptance (Fmin : ℚ) : verifyAccumulator emptyAccumulator Fmin = true ↔
    Fmin ≤ 1 := by rw [verify_accept_iff]; simp [emptyAccumulator]

theorem empty_accumulator_valid (Fmin : ℚ) (hF : Fmin ≤ 1) :
    verifyAccumulator emptyAccumulator Fmin = true := (empty_acceptance Fmin).mpr hF

theorem foldStep_index_independent (acc : IVCAccumulator) (w : StepWitness) (index : ℕ) :
    foldStep acc { w with stepIndex := index } = foldStep acc w := rfl

/-- Eager symbolic expression evaluator; each leaf and conjunction costs one unit. -/
inductive VerifierExpr
  | ReadValid
  | FidelityCompare
  | And (left right : VerifierExpr)
  deriving DecidableEq, Repr

def evalVerifierExpr (acc : IVCAccumulator) (Fmin : ℚ) : VerifierExpr → Bool × ℕ
  | .ReadValid => (acc.allValid, 1)
  | .FidelityCompare => (decide (Fmin ≤ acc.accumulatedFidelity), 1)
  | .And left right =>
    let l := evalVerifierExpr acc Fmin left
    let r := evalVerifierExpr acc Fmin right
    (l.1 && r.1, l.2 + r.2 + 1)

def verificationExpression : VerifierExpr := .And .ReadValid .FidelityCompare

theorem verification_constant_time_model (acc : IVCAccumulator) (Fmin : ℚ) :
    evalVerifierExpr acc Fmin verificationExpression = (verifyAccumulator acc Fmin, 3) := rfl

theorem verification_cost_history_independent (a b : IVCAccumulator) (Fa Fb : ℚ) :
    (evalVerifierExpr a Fa verificationExpression).2 =
      (evalVerifierExpr b Fb verificationExpression).2 := rfl

structure QuantumIVCAccumulatorSuite : Prop where
  bounds : ∀ (acc : IVCAccumulator) (w : StepWitness),
    0 ≤ (foldStep acc w).accumulatedFidelity ∧ (foldStep acc w).accumulatedFidelity ≤ 1
  soundness : ∀ (acc : IVCAccumulator) (w : StepWitness),
    acc.allValid = true → w.valid = true → (foldStep acc w).allValid = true
  false_absorbing : ∀ (acc : IVCAccumulator) (ws : List StepWitness),
    acc.allValid = false → (foldSteps acc ws).allValid = false
  exact_loss : ∀ (acc : IVCAccumulator) (ws : List StepWitness),
    (foldSteps acc ws).accumulatedFidelity = max 0 (acc.accumulatedFidelity - totalLoss ws)
  linear_bound : ∀ (acc : IVCAccumulator) (ws : List StepWitness) (eps : ℚ),
    0 ≤ eps → (∀ w ∈ ws, w.fidelityLoss ≤ eps) →
    max 0 (acc.accumulatedFidelity - (ws.length : ℚ) * eps) ≤
      (foldSteps acc ws).accumulatedFidelity
  validity : ∀ (acc : IVCAccumulator) (ws : List StepWitness),
    (foldSteps acc ws).allValid = true ↔ acc.allValid = true ∧ ∀ w ∈ ws, w.valid = true
  semantic_soundness : ∀ (R : StepWitness → Prop) (acc : IVCAccumulator)
    (ws : List StepWitness) (Fmin : ℚ),
    (∀ w ∈ ws, w.valid = true → R w) →
    verifyAccumulator (foldSteps acc ws) Fmin = true → ∀ w ∈ ws, R w
  count : ∀ (acc : IVCAccumulator) (ws : List StepWitness),
    (foldSteps acc ws).totalSteps = acc.totalSteps + ws.length
  bad_witness_suffix : ∀ (acc : IVCAccumulator) (w : StepWitness) (ws : List StepWitness),
    w.valid = false → (foldSteps (foldStep acc w) ws).allValid = false
  empty_valid : ∀ (Fmin : ℚ), Fmin ≤ 1 → verifyAccumulator emptyAccumulator Fmin = true
  symbolic_cost : ∀ (acc : IVCAccumulator) (Fmin : ℚ),
    evalVerifierExpr acc Fmin verificationExpression = (verifyAccumulator acc Fmin, 3)
  index_independent : ∀ (acc : IVCAccumulator) (w : StepWitness) (index : ℕ),
    foldStep acc { w with stepIndex := index } = foldStep acc w

theorem verification_suite : QuantumIVCAccumulatorSuite := {
  bounds := fold_fidelity_bounds
  soundness := fold_soundness_preservation
  false_absorbing := falsity_absorption
  exact_loss := exact_fidelity_after_fold
  linear_bound := linear_fidelity_lower_bound
  validity := all_valid_iff
  semantic_soundness := conditional_semantic_soundness
  count := count_after_fold
  bad_witness_suffix := folding_falsity_absorption
  empty_valid := empty_accumulator_valid
  symbolic_cost := verification_constant_time_model
  index_independent := foldStep_index_independent
}

end QuantumIVCAccumulatorContract

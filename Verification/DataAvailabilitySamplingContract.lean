/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Finite uniform sampling with replacement

Uniformity is over all functions from sample positions to shard indices. Coordinates
are independent and duplicates are allowed. Probability is a cardinality ratio.
The count threshold alone is a definition; algebraic recovery is stated separately.
The sampling count is not a bound on bytes, hardware cost or network availability.
-/
namespace DataAvailabilitySamplingContract

structure RSBlockParams where
  k : ℕ
  n : ℕ
  hk_pos : 0 < k
  hn_eq : n = 2 * k

structure BlockAvailabilityState (params : RSBlockParams) where
  availableShards : ℕ
  h_le : availableShards ≤ params.n

def isRecoverable (params : RSBlockParams) (state : BlockAvailabilityState params) : Prop :=
  params.k ≤ state.availableShards

/-- This is the specified count predicate, not a standalone decoder theorem. -/
theorem mds_recovery_threshold (params : RSBlockParams) (state : BlockAvailabilityState params) :
    isRecoverable params state ↔ params.k ≤ state.availableShards := Iff.rfl

theorem shard_count_positive (params : RSBlockParams) : 0 < params.n := by
  have hk := params.hk_pos
  rw [params.hn_eq]
  omega

theorem unrecoverable_erasure_bound (params : RSBlockParams)
    (state : BlockAvailabilityState params) :
    ¬ isRecoverable params state ↔ params.k < params.n - state.availableShards := by
  unfold isRecoverable
  have h := params.hn_eq
  omega

abbrev SamplingTrace (n S : ℕ) := Fin S → Fin n

abbrev SuccessfulTrace {n : ℕ} (available : Finset (Fin n)) (S : ℕ) :=
  { trace : SamplingTrace n S // ∀ i, trace i ∈ available }

def successfulTraceEquiv {n : ℕ} (available : Finset (Fin n)) (S : ℕ) :
    SuccessfulTrace available S ≃ (Fin S → { x : Fin n // x ∈ available }) where
  toFun t i := ⟨t.1 i, t.2 i⟩
  invFun t := ⟨fun i => (t i).1, fun i => (t i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem successful_trace_count {n : ℕ} (available : Finset (Fin n)) (S : ℕ) :
    Fintype.card (SuccessfulTrace available S) = available.card ^ S := by
  rw [Fintype.card_congr (successfulTraceEquiv available S)]
  simp

theorem all_trace_count (n S : ℕ) : Fintype.card (SamplingTrace n S) = n ^ S := by
  simp [SamplingTrace]

/-- Uniform success probability when n>0; at n=0 this is only a totalized ratio. -/
def samplingSuccessProbability {n : ℕ} (available : Finset (Fin n)) (S : ℕ) : ℚ :=
  (Fintype.card (SuccessfulTrace available S) : ℚ) /
    (Fintype.card (SamplingTrace n S) : ℚ)

theorem sampling_probability_formula {n : ℕ} (available : Finset (Fin n)) (S : ℕ) :
    samplingSuccessProbability available S = ((available.card : ℚ) / (n : ℚ)) ^ S := by
  rw [samplingSuccessProbability, successful_trace_count, all_trace_count]
  simp [div_pow]

def maxDeceptionProbability (_params : RSBlockParams) (S : ℕ) : ℚ := (1 / 2) ^ S

theorem availability_fraction_bounds {n : ℕ} (hn : 0 < n) (available : Finset (Fin n)) :
    0 ≤ (available.card : ℚ) / (n : ℚ) ∧ (available.card : ℚ) / (n : ℚ) ≤ 1 := by
  have hc : available.card ≤ n := by simpa using Finset.card_le_univ available
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  exact ⟨div_nonneg (Nat.cast_nonneg _) hnq.le,
    (div_le_one hnq).mpr (by exact_mod_cast hc)⟩

theorem sampling_probability_bounds {n : ℕ} (hn : 0 < n)
    (available : Finset (Fin n)) (S : ℕ) :
    0 ≤ samplingSuccessProbability available S ∧ samplingSuccessProbability available S ≤ 1 := by
  rw [sampling_probability_formula]
  have h := availability_fraction_bounds hn available
  exact ⟨pow_nonneg h.1 _, pow_le_one₀ h.1 h.2⟩

theorem sampling_probability_antitone {n : ℕ} (hn : 0 < n)
    (available : Finset (Fin n)) : Antitone (samplingSuccessProbability available) := by
  have h := availability_fraction_bounds hn available
  intro s t hst
  simp only [sampling_probability_formula]
  exact pow_le_pow_of_le_one h.1 h.2 hst

theorem unrecoverable_fraction_bound (params : RSBlockParams)
    (available : Finset (Fin params.n)) (hu : available.card < params.k) :
    (available.card : ℚ) / (params.n : ℚ) ≤ 1 / 2 := by
  have hnq : (0 : ℚ) < params.n := by exact_mod_cast shard_count_positive params
  have hkq : (available.card : ℚ) < params.k := by exact_mod_cast hu
  have heq : (params.n : ℚ) = 2 * (params.k : ℚ) := by exact_mod_cast params.hn_eq
  apply (div_le_iff₀ hnq).mpr
  linarith

theorem sampling_deception_decay (params : RSBlockParams)
    (available : Finset (Fin params.n)) (S : ℕ) (hu : available.card < params.k) :
    samplingSuccessProbability available S ≤ maxDeceptionProbability params S := by
  rw [sampling_probability_formula]
  exact pow_le_pow_left₀ (availability_fraction_bounds (shard_count_positive params) available).1
    (unrecoverable_fraction_bound params available hu) S

theorem max_deception_strict_decay (params : RSBlockParams) :
    StrictAnti (maxDeceptionProbability params) :=
  pow_right_strictAnti₀ (by norm_num : (0 : ℚ) < 1 / 2) (by norm_num : (1 / 2 : ℚ) < 1)

theorem sampling_security_exponential_bound (params : RSBlockParams) :
    maxDeceptionProbability params 20 = 1 / 1048576 ∧
      maxDeceptionProbability params 20 < 1 / 1000000 := by
  norm_num [maxDeceptionProbability]

theorem twenty_sample_security (params : RSBlockParams)
    (available : Finset (Fin params.n)) (hu : available.card < params.k) :
    samplingSuccessProbability available 20 < 1 / 1000000 :=
  (sampling_deception_decay params available 20 hu).trans_lt
    (sampling_security_exponential_bound params).2

theorem ceiling_parameter_independent (p q : RSBlockParams) (S : ℕ) :
    maxDeceptionProbability p S = maxDeceptionProbability q S := rfl

theorem max_deception_positive (params : RSBlockParams) (S : ℕ) :
    0 < maxDeceptionProbability params S := pow_pos (by norm_num : (0 : ℚ) < 1 / 2) S

theorem max_deception_nonnegative (params : RSBlockParams) (S : ℕ) :
    0 ≤ maxDeceptionProbability params S := (max_deception_positive params S).le

def stateOfAvailable (params : RSBlockParams) (a : Finset (Fin params.n)) :
    BlockAvailabilityState params :=
  ⟨a.card, by simpa using Finset.card_le_univ a⟩

theorem actual_set_recoverable_iff (params : RSBlockParams) (a : Finset (Fin params.n)) :
    isRecoverable params (stateOfAvailable params a) ↔ params.k ≤ a.card := Iff.rfl

/-- Exactly twenty positions are queried; only the stated size premise makes this fewer. -/
theorem light_client_verification_model (params : RSBlockParams) (hsize : 20 < params.n) :
    Fintype.card (Fin 20) = 20 ∧ Fintype.card (Fin 20) < params.n ∧
      maxDeceptionProbability params 20 < 1 / 1000000 :=
  ⟨Fintype.card_fin 20, by simpa using hsize, (sampling_security_exponential_bound params).2⟩


open Polynomial

section PolynomialCore

variable {F : Type*} [Field F] {ι : Type*}

/-- At least k distinct authentic evaluation nodes determine a polynomial of degree < k. -/
theorem mds_unique_of_card_le (selected : Finset ι) (nodes : ι → F)
    (h_distinct : Set.InjOn nodes selected) (k : ℕ) (h_count : k ≤ selected.card)
    (p q : F[X]) (hp : p.degree < k) (hq : q.degree < k)
    (h_eval : ∀ i ∈ selected, p.eval (nodes i) = q.eval (nodes i)) : p = q := by
  have h_count' : (k : WithBot ℕ) ≤ (selected.card : WithBot ℕ) := by
    exact_mod_cast h_count
  exact Polynomial.eq_of_degrees_lt_of_eval_index_eq selected h_distinct
    (hp.trans_le h_count') (hq.trans_le h_count') h_eval

/-- Lagrange interpolation on the actual selected nodes recovers the authentic polynomial. -/
theorem mds_interpolate_authentic [DecidableEq ι] (selected : Finset ι) (nodes values : ι → F)
    (h_distinct : Set.InjOn nodes selected) (k : ℕ) (h_count : k ≤ selected.card)
    (p : F[X]) (hp : p.degree < k)
    (h_authentic : ∀ i ∈ selected, values i = p.eval (nodes i)) :
    Lagrange.interpolate selected nodes values = p := by
  have h_count' : (k : WithBot ℕ) ≤ (selected.card : WithBot ℕ) := by
    exact_mod_cast h_count
  exact (Lagrange.eq_interpolate_of_eval_eq values h_distinct
    (hp.trans_le h_count') (fun i hi => (h_authentic i hi).symm)).symm

/-- Existence is witnessed by the explicit interpolant; uniqueness uses actual evaluations. -/
theorem mds_existsUnique_authentic (selected : Finset ι) (nodes values : ι → F)
    (h_distinct : Set.InjOn nodes selected) (k : ℕ) (h_count : k ≤ selected.card)
    (p : F[X]) (hp : p.degree < k)
    (h_authentic : ∀ i ∈ selected, values i = p.eval (nodes i)) :
    ∃! q : F[X], q.degree < k ∧ ∀ i ∈ selected, q.eval (nodes i) = values i := by
  classical
  have hreconstruct := mds_interpolate_authentic selected nodes values h_distinct
    k h_count p hp h_authentic
  refine ⟨Lagrange.interpolate selected nodes values, ?_, ?_⟩
  · exact ⟨by simpa only [hreconstruct] using hp,
      fun i hi => Lagrange.eval_interpolate_at_node values h_distinct hi⟩
  · intro q hq
    rw [hreconstruct]
    exact mds_unique_of_card_le selected nodes h_distinct k h_count q p hq.1 hp
      (fun i hi => (hq.2 i hi).trans (h_authentic i hi))

/-- Fewer than k supplied nodes cannot universally distinguish all degree-<k polynomials.
The zero polynomial and the nonzero nodal polynomial agree on every selected node.
This establishes failure of universal uniqueness, not a claim about a particular decoder. -/
theorem shortage_two_polynomials (selected : Finset ι) (nodes : ι → F)
    (k : ℕ) (h_count : selected.card < k) :
    ∃ p q : F[X], p ≠ q ∧ p.degree < k ∧ q.degree < k ∧
      ∀ i ∈ selected, p.eval (nodes i) = q.eval (nodes i) := by
  refine ⟨0, Lagrange.nodal selected nodes, ?_, ?_, ?_, ?_⟩
  · exact Ne.symm Lagrange.nodal_ne_zero
  · simp only [Polynomial.degree_zero]
    exact WithBot.bot_lt_coe k
  · rw [Lagrange.degree_nodal]
    exact_mod_cast h_count
  · intro i hi
    rw [Polynomial.eval_zero, Lagrange.eval_nodal_at_node hi]

end PolynomialCore


theorem recoverable_polynomial_reconstruction {F : Type*} [Field F]
    (params : RSBlockParams) (a : Finset (Fin params.n)) (nodes values : Fin params.n → F)
    (hd : Set.InjOn nodes a) (p : F[X]) (hp : p.degree < params.k)
    (ha : ∀ i ∈ a, values i = p.eval (nodes i))
    (hr : isRecoverable params (stateOfAvailable params a)) :
    Lagrange.interpolate a nodes values = p :=
  mds_interpolate_authentic a nodes values hd params.k hr p hp ha

structure DataAvailabilitySamplingSuite : Prop where
  threshold : ∀ (p : RSBlockParams) (s : BlockAvailabilityState p),
    isRecoverable p s ↔ p.k ≤ s.availableShards
  erasures : ∀ (p : RSBlockParams) (s : BlockAvailabilityState p),
    ¬ isRecoverable p s ↔ p.k < p.n - s.availableShards
  trace_count : ∀ (n S : ℕ) (a : Finset (Fin n)),
    Fintype.card (SuccessfulTrace a S) = a.card ^ S
  probability : ∀ (n S : ℕ) (a : Finset (Fin n)),
    samplingSuccessProbability a S = ((a.card : ℚ) / (n : ℚ)) ^ S
  ceiling : ∀ (p : RSBlockParams) (a : Finset (Fin p.n)) (S : ℕ), a.card < p.k →
    samplingSuccessProbability a S ≤ maxDeceptionProbability p S
  twenty : ∀ (p : RSBlockParams), maxDeceptionProbability p 20 < 1 / 1000000
  parameter_independence : ∀ (p q : RSBlockParams) (S : ℕ),
    maxDeceptionProbability p S = maxDeceptionProbability q S
  probability_bounds : ∀ (p : RSBlockParams) (a : Finset (Fin p.n)) (S : ℕ),
    0 ≤ samplingSuccessProbability a S ∧ samplingSuccessProbability a S ≤ 1
  sample_antitone : ∀ (p : RSBlockParams) (a : Finset (Fin p.n)),
    Antitone (samplingSuccessProbability a)
  positive_ceiling : ∀ (p : RSBlockParams) (S : ℕ), 0 < maxDeceptionProbability p S
  light_client : ∀ (p : RSBlockParams), 20 < p.n →
    Fintype.card (Fin 20) = 20 ∧ Fintype.card (Fin 20) < p.n ∧
      maxDeceptionProbability p 20 < 1 / 1000000
  polynomial_reconstruction : ∀ (F : Type) [Field F] (params : RSBlockParams)
    (a : Finset (Fin params.n)) (nodes values : Fin params.n → F),
    Set.InjOn nodes a → ∀ (p : F[X]), p.degree < params.k →
    (∀ i ∈ a, values i = p.eval (nodes i)) →
    isRecoverable params (stateOfAvailable params a) → Lagrange.interpolate a nodes values = p

theorem verification_suite : DataAvailabilitySamplingSuite := {
  threshold := mds_recovery_threshold
  erasures := unrecoverable_erasure_bound
  trace_count := fun _ S a => successful_trace_count a S
  probability := fun _ S a => sampling_probability_formula a S
  ceiling := sampling_deception_decay
  twenty := fun p => (sampling_security_exponential_bound p).2
  parameter_independence := ceiling_parameter_independent
  probability_bounds := fun p a S => sampling_probability_bounds (shard_count_positive p) a S
  sample_antitone := fun p a => sampling_probability_antitone (shard_count_positive p) a
  positive_ceiling := max_deception_positive
  light_client := light_client_verification_model
  polynomial_reconstruction := fun _ _ => recoverable_polynomial_reconstruction
}

end DataAvailabilitySamplingContract

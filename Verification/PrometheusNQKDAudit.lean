/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBB84ProtocolQBER

/-!
# Ideal-qubit intercept--resend and limits of universal disturbance claims

The imported core already constructs complex two-dimensional BB84 kets, normalized
projectors, Born branches and their finite joint experiment. This module reuses
that derivation, adds an independent binary-noise product experiment, a general
pure-state projective return calculation and a noninformative instrument.
Neutrino Majorana/OAM preparation as these qubits is not proved. Neither arbitrary
attack security nor composable key security is claimed. Uninformative measurements
and measurement in a known orthogonal preparation basis need not disturb states.
-/
namespace PrometheusNQKDAudit
noncomputable section
open QuantumBB84ProtocolQBER
open scoped BigOperators ComplexOrder

/-- Reused actual complex-ket normalization, not normalization of a label-only model. -/
theorem normalized_states (b : BB84Basis) (x : BB84Bit) :
    (ket b x).conjTranspose * ket b x = 1 := ket_normalized b x

theorem cross_basis_overlap (x y : BB84Bit) : transition 0 1 x y = 1 / 2 :=
  born_rule_diff_basis 0 1 (by decide) x y

theorem cross_basis_nonorthogonal (x y : BB84Bit) :
    0 < transition 0 1 x y ∧ transition 0 1 x y < 1 := by
  rw [cross_basis_overlap]
  norm_num

/-- An overlap below one alone does not establish nonorthogonality. -/
theorem orthogonal_endpoint_counterexample :
    transition 0 0 0 1 = 0 ∧ transition 0 0 0 1 < 1 := by
  norm_num [transition_exact]

/-- Existing Born-branch experiment: independent uniform choices, then positive-mass sifting. -/
theorem born_intercept_quarter :
    attackLaw.probability Sifted = 1 / 2 ∧
      attackLaw.probability (fun ω => Error ω ∧ Sifted ω) = 1 / 8 ∧
      qber attackLaw = 1 / 4 :=
  ⟨sifting_probability_half, intercept_resend_joint_error_sifting, intercept_resend_error_exact⟩

theorem partial_interception_positive (f : ℝ) (hf : 0 < f) (hf1 : f ≤ 1) :
    0 < qber (partialLaw f (le_of_lt hf) hf1) := by
  rw [partial_intercept_qber]
  positivity

/-- A flip coin independent of all round coordinates; no baseline-noise independence is inferred. -/
def flipWeight (p : ℝ) (flip : Bool) : ℝ := if flip then p else 1 - p

def noisyLaw (L : FiniteLaw Round) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (Round × Bool) where
  weight ω := L.weight ω.1 * flipWeight p ω.2
  nonneg ω := mul_nonneg (L.nonneg _) (by
    cases ω.2 <;> simp only [flipWeight, Bool.false_eq_true, if_false, if_true]
    · exact sub_nonneg.mpr hp1
    · exact hp)
  normalized := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, flipWeight, Bool.false_eq_true, if_false, if_true]
    have he (ω : Round) : L.weight ω * p + L.weight ω * (1 - p) = L.weight ω := by ring
    simpa only [he] using L.normalized

def NoisyError (ω : Round × Bool) : Prop := if ω.2 then ¬ Error ω.1 else Error ω.1
def NoisySifted (ω : Round × Bool) : Prop := Sifted ω.1
instance : DecidablePred NoisyError := fun _ => inferInstanceAs (Decidable (ite _ _ _))
instance : DecidablePred NoisySifted := fun _ => inferInstanceAs (Decidable (Sifted _))

theorem noisy_sifting (L : FiniteLaw Round) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (noisyLaw L p hp hp1).probability NoisySifted = L.probability Sifted := by
  unfold FiniteLaw.probability
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hs : Sifted ω <;>
    simp [NoisySifted, noisyLaw, flipWeight, hs]
  ring

theorem sifted_complement (L : FiniteLaw Round) :
    L.probability (fun ω => ¬ Error ω ∧ Sifted ω) =
      L.probability Sifted - L.probability (fun ω => Error ω ∧ Sifted ω) := by
  unfold FiniteLaw.probability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : Error ω <;> by_cases hs : Sifted ω <;> simp [he, hs]

theorem noisy_joint_error (L : FiniteLaw Round) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (noisyLaw L p hp hp1).probability (fun ω => NoisyError ω ∧ NoisySifted ω) =
      (1 - p) * L.probability (fun ω => Error ω ∧ Sifted ω) +
        p * L.probability (fun ω => ¬ Error ω ∧ Sifted ω) := by
  unfold FiniteLaw.probability
  rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : Error ω <;> by_cases hs : Sifted ω <;>
    simp [NoisyError, NoisySifted, noisyLaw, flipWeight, he, hs] <;> ring

def noisyQber (L : FiniteLaw Round) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : ℝ :=
  (noisyLaw L p hp hp1).probability (fun ω => NoisyError ω ∧ NoisySifted ω) /
    (noisyLaw L p hp hp1).probability NoisySifted

/-- Derived from the normalized product law, with sifting probability one half. -/
theorem independent_baseline_qber (f p : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    noisyQber (partialLaw f hf hf1) p hp hp1 = p + (1 - 2 * p) * f / 4 := by
  unfold noisyQber
  rw [noisy_sifting, noisy_joint_error, sifted_complement, partial_sifting_probability,
    partial_probability, honest_joint_error_sifting, intercept_resend_joint_error_sifting]
  ring

theorem baseline_increase (f p : ℝ) (hf : 0 < f) (hf1 : f ≤ 1)
    (hp : 0 ≤ p) (hpHalf : p < 1 / 2) :
    p < noisyQber (partialLaw f (le_of_lt hf) hf1) p hp (by linarith) := by
  rw [independent_baseline_qber]
  have h := mul_pos (show 0 < 1 - 2 * p by linarith) hf
  linarith

/-- Scalar no-error factor for an IID sample; positivity is not guaranteed detection. -/
theorem finite_iid_no_error_positive (f : ℝ) (_hf : 0 ≤ f) (hf1 : f ≤ 1) (m : ℕ) :
    0 < (1 - f / 4) ^ m := by
  exact pow_pos (by linarith) m

/-- The same binary-flip law, rearranged. This does not establish an Rz implementation. -/
theorem baseline_rearranged (f p : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    noisyQber (partialLaw f hf hf1) p hp hp1 = f / 4 + (1 - f / 2) * p := by
  rw [independent_baseline_qber]
  ring

/-- An arbitrary pure vector in complex dimension two, represented as a column. -/
def pureDensity (v : Matrix (Fin 2) (Fin 1) ℂ) : QMatrix := v * v.conjTranspose

theorem pure_positive (v : Matrix (Fin 2) (Fin 1) ℂ) : (pureDensity v).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose v

theorem pure_trace (v : Matrix (Fin 2) (Fin 1) ℂ) (hv : v.conjTranspose * v = 1) :
    (pureDensity v).trace = 1 := by
  rw [pureDensity, Matrix.trace_mul_comm, hv]
  simp [Matrix.trace]

theorem pure_projector (v : Matrix (Fin 2) (Fin 1) ℂ) (hv : v.conjTranspose * v = 1) :
    pureDensity v * pureDensity v = pureDensity v := by
  unfold pureDensity
  calc
    v * v.conjTranspose * (v * v.conjTranspose) = v * (v.conjTranspose * v) * v.conjTranspose :=
      by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hv, Matrix.mul_one]

/-- Complete rank-one projective measurement with the outcome forgotten. -/
def dephase (basis : BB84Basis) (rho : QMatrix) : QMatrix :=
  P basis 0 * rho * P basis 0 + P basis 1 * rho * P basis 1

theorem dephase_trace (basis : BB84Basis) (rho : QMatrix) :
    (dephase basis rho).trace = rho.trace := by
  have ht (x : BB84Bit) : (P basis x * rho * P basis x).trace = (P basis x * rho).trace := by
    rw [Matrix.trace_mul_cycle, projector_orthogonal]
    simp
  rw [dephase, Matrix.trace_add, ht, ht, ← Matrix.trace_add, ← Matrix.add_mul,
    projector_complete, Matrix.one_mul]

/-- Return contribution of each measured-and-reprepared branch is the squared Born overlap. -/
theorem return_branch (rho : QMatrix) (hrho : rho.PosSemidef) (basis : BB84Basis)
    (x : BB84Bit) :
    (rho * (P basis x * rho * P basis x)).trace.re = (born basis x rho) ^ 2 := by
  have ht : (rho * P basis x).trace = (P basis x * rho).trace :=
    Matrix.trace_mul_comm _ _
  rw [measure_prepare_exact, Matrix.mul_smul, Matrix.trace_smul, ht,
    ← born_complex_eq rho hrho basis x]
  simp [smul_eq_mul, Complex.mul_re]
  ring

def wrongReturn (basis : BB84Basis) (v : Matrix (Fin 2) (Fin 1) ℂ) : ℝ :=
  (((1 - pureDensity v) * dephase basis (pureDensity v)).trace).re

/-- The two Born branches derive 2c(1-c); nonorthogonality requires both strict bounds. -/
theorem pure_wrong_return_exact (basis : BB84Basis) (v : Matrix (Fin 2) (Fin 1) ℂ)
    (hv : v.conjTranspose * v = 1) :
    wrongReturn basis v = 2 * born basis 0 (pureDensity v) *
      (1 - born basis 0 (pureDensity v)) := by
  have ht := pure_trace v hv
  have hn := born_normalized (pureDensity v) ht basis
  simp only [Fin.sum_univ_two] at hn
  unfold wrongReturn
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re, dephase_trace, ht]
  simp only [Complex.one_re]
  rw [dephase, Matrix.mul_add, Matrix.trace_add, Complex.add_re,
    return_branch _ (pure_positive v), return_branch _ (pure_positive v)]
  nlinarith [sq_nonneg (born basis 0 (pureDensity v))]

theorem nonorthogonal_return_disturbance (basis : BB84Basis)
    (v : Matrix (Fin 2) (Fin 1) ℂ) (hv : v.conjTranspose * v = 1)
    (hc : 0 < born basis 0 (pureDensity v)) (hc1 : born basis 0 (pureDensity v) < 1) :
    0 < wrongReturn basis v := by
  rw [pure_wrong_return_exact basis v hv]
  positivity

/-- Two noninformative Kraus outcomes, each proportional to the identity. -/
def coinKraus (_outcome : BB84Bit) : QMatrix := (rootTwo / 2 : ℂ) • 1

def coinChannel (rho : QMatrix) : QMatrix :=
  ∑ x : BB84Bit, coinKraus x * rho * (coinKraus x).conjTranspose

theorem coin_branch (rho : QMatrix) (x : BB84Bit) :
    coinKraus x * rho * (coinKraus x).conjTranspose = (1 / 2 : ℂ) • rho := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [coinKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num <;> ring

theorem coin_kraus_complete :
    (∑ x : BB84Bit, (coinKraus x).conjTranspose * coinKraus x) = 1 := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [coinKraus, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    ring_nf <;> norm_num

theorem coin_channel_identity (rho : QMatrix) : coinChannel rho = rho := by
  simp only [coinChannel, Fin.sum_univ_two, coin_branch]
  ext i j : 2
  simp
  ring

theorem coin_outcome_independent (rho : QMatrix) (ht : rho.trace = 1) (x : BB84Bit) :
    (coinKraus x * rho * (coinKraus x).conjTranspose).trace = 1 / 2 := by
  rw [coin_branch, Matrix.trace_smul, ht]
  simp

/-- An actual complete two-outcome instrument can leave every state unchanged. -/
theorem noninformative_counterexample (b : BB84Basis) (x : BB84Bit) :
    transition b b x x = 1 ∧ coinChannel (P b x) = P b x := by
  exact ⟨by simp [transition_exact], coin_channel_identity _⟩

theorem known_basis_nondisturbance (b : BB84Basis) (x : BB84Bit) :
    dephase b (P b x) = P b x := by
  fin_cases b <;> fin_cases x <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    norm_num [dephase, projector_exact, projectorTable, Matrix.mul_apply, Fin.sum_univ_two]

structure PrometheusNQKDAuditSuite : Prop where
  normalization : ∀ b x, (ket b x).conjTranspose * ket b x = 1
  overlap : ∀ x y, 0 < transition 0 1 x y ∧ transition 0 1 x y < 1
  intercepted : qber attackLaw = 1 / 4
  partial_error : ∀ f hf hf1, qber (partialLaw f hf hf1) = f / 4
  baseline : ∀ f p hf hf1 hp hp1,
    noisyQber (partialLaw f hf hf1) p hp hp1 = p + (1 - 2 * p) * f / 4
  counterexample : ∀ rho, coinChannel rho = rho

theorem verification_suite : PrometheusNQKDAuditSuite :=
  ⟨normalized_states, cross_basis_nonorthogonal, intercept_resend_error_exact,
    partial_intercept_qber, independent_baseline_qber, coin_channel_identity⟩
end
end PrometheusNQKDAudit

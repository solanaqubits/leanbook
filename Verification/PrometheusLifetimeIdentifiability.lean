/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Two adjacent equal-duration beta bins and one terminal survivor count.
N is the mean of a Poisson initial ensemble, not a fixed integer population.
Known efficiencies/backgrounds. Independent Poisson sampling is the explicit model.
-/
namespace PrometheusLifetimeIdentifiability
noncomputable section
open Matrix
open scoped BigOperators

def survival (h g : ℝ) : ℝ := Real.exp (-g * h)
def exposure (h g : ℝ) : ℝ := (1 - survival h g) / g
def exposureSlope (h g : ℝ) : ℝ := (h * g * survival h g - (1 - survival h g)) / g^2

theorem survival_derivative (h g : ℝ) :
    HasDerivAt (survival h) (-h * survival h g) g := by
  have H : HasDerivAt (fun z : ℝ => Real.exp (-z * h))
      (Real.exp (-g*h) * (-1*h)) g := (((hasDerivAt_id g).neg.mul_const h).exp)
  exact H.congr_deriv (by dsimp [survival]; ring)

theorem exposure_derivative (h g : ℝ) (hg : g ≠ 0) :
    HasDerivAt (exposure h) (exposureSlope h g) g := by
  have H : HasDerivAt (fun z : ℝ => (1 - survival h z) / z)
      (((0 - (-h * survival h g)) * g - (1 - survival h g) * 1) / g^2) g :=
    ((hasDerivAt_const g (1 : ℝ)).sub (survival_derivative h g)).div
      (hasDerivAt_id g) hg
  have he : exposureSlope h g =
      ((0 - (-h * survival h g)) * g - (1 - survival h g) * 1) / g^2 := by
    unfold exposureSlope
    ring
  rw [he]
  exact H

theorem survival_bounds (h g : ℝ) (hh : 0 < h) (hg : 0 < g) :
    0 < survival h g ∧ survival h g < 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  apply Real.exp_lt_one_iff.mpr
  nlinarith

theorem exposure_pos (h g : ℝ) (hh : 0 < h) (hg : 0 < g) :
    0 < exposure h g := div_pos (sub_pos.mpr (survival_bounds h g hh hg).2) hg

def amplitude (eb b N h g : ℝ) : ℝ := eb * b * N * exposure h g

def means (eb es h b loss N : ℝ) (B : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let g := b + loss
  ![amplitude eb b N h g + B 0,
    amplitude eb b N h g * survival h g + B 1,
    es * N * (survival h g)^2 + B 2]

/-- Poisson log likelihood, with parameter-independent factorial terms retained. -/
def logLikelihood (mu : Fin 3 → ℝ) (counts : Fin 3 → ℕ) : ℝ :=
  ∑ i, ((counts i : ℝ) * Real.log (mu i) - mu i - Real.log (Nat.factorial (counts i)))

/-- Chain factors: (b,loss,N) to (b,g,N), then (A,u,V), then (A,A*u,V). -/
def rateTransform : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0; 1,1,0; 0,0,1]
def latentJac (eb es h b g N : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let u := survival h g
  let a := exposure h g
  !![eb*N*a, eb*b*N*exposureSlope h g, eb*b*a;
     0, -h*u, 0;
     0, -2*h*es*N*u^2, es*u^2]
def observationJac (A u : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1,0,0; u,A,0; 0,0,1]
def jacobian (eb es h b loss N : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  observationJac (amplitude eb b N h (b+loss)) (survival h (b+loss)) *
    latentJac eb es h b (b+loss) N * rateTransform

/-- The displayed matrix really differentiates the mean vector along scalar curves. -/
theorem means_directional {b loss N : ℝ → ℝ} {x db dl dN : ℝ}
    (eb es h : ℝ) (B : Fin 3 → ℝ)
    (hb : HasDerivAt b db x) (hl : HasDerivAt loss dl x) (hN : HasDerivAt N dN x)
    (hg : b x + loss x ≠ 0) (i : Fin 3) :
    HasDerivAt (fun t => means eb es h (b t) (loss t) (N t) B i)
      ((jacobian eb es h (b x) (loss x) (N x) *ᵥ ![db,dl,dN]) i) x := by
  have hsum : HasDerivAt (fun t => b t + loss t) (db + dl) x := hb.add hl
  have hu : HasDerivAt (fun t => survival h (b t + loss t))
      (-h * survival h (b x + loss x) * (db + dl)) x :=
    HasDerivAt.comp (h₂ := survival h) (h := fun t => b t + loss t) x
      (survival_derivative h (b x + loss x)) hsum
  have ha : HasDerivAt (fun t => exposure h (b t + loss t))
      (exposureSlope h (b x + loss x) * (db + dl)) x :=
    HasDerivAt.comp (h₂ := exposure h) (h := fun t => b t + loss t) x
      (exposure_derivative h (b x + loss x) hg) hsum
  have hA := (((hb.const_mul eb).mul hN).mul ha)
  fin_cases i
  · have H := hA.add_const (B 0)
    exact H.congr_deriv (by
      simp [jacobian, observationJac, latentJac, rateTransform, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, amplitude]
      ring)
  · have H := (hA.mul hu).add_const (B 1)
    exact H.congr_deriv (by
      simp [jacobian, observationJac, latentJac, rateTransform, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, amplitude]
      ring)
  · have H := ((hN.const_mul es).mul (hu.pow 2)).add_const (B 2)
    exact H.congr_deriv (by
      simp [jacobian, observationJac, latentJac, rateTransform, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ, amplitude]
      ring)

theorem jacobian_det (eb es h b loss N : ℝ) :
    (jacobian eb es h b loss N).det =
      -(eb^2 * es * b * N^2 * h * (survival h (b+loss))^3 * (exposure h (b+loss))^2) := by
  simp [jacobian, observationJac, latentJac, rateTransform,
    Matrix.det_fin_three, amplitude]
  ring

def fisher (J : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ := J.transpose * Matrix.diagonal (fun i => (mu i)⁻¹) * J

theorem fisher_det (J : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ) :
    (fisher J mu).det = J.det^2 * ∏ i, (mu i)⁻¹ := by
  simp only [fisher, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem fisher_posDef (J : Matrix (Fin 3) (Fin 3) ℝ) (mu : Fin 3 → ℝ)
    (hJ : J.det ≠ 0) (hm : ∀ i, 0 < mu i) : (fisher J mu).PosDef := by
  have hu : IsUnit J := J.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hJ)
  have hd : (Matrix.diagonal fun i => (mu i)⁻¹).PosDef :=
    Matrix.posDef_diagonal_iff.mpr (fun i => inv_pos.mpr (hm i))
  simpa [fisher, Matrix.star_eq_conjTranspose] using
    hu.posDef_star_left_conjugate_iff.mpr hd

theorem means_pos (eb es h b loss N : ℝ) (B : Fin 3 → ℝ)
    (heb : 0 < eb) (hes : 0 < es) (hh : 0 < h) (hb : 0 < b)
    (hl : 0 ≤ loss) (hN : 0 < N) (hB : ∀ i, 0 ≤ B i) :
    ∀ i, 0 < means eb es h b loss N B i := by
  have hg : 0 < b+loss := by linarith
  have hu := (survival_bounds h (b+loss) hh hg).1
  have ha : 0 < amplitude eb b N h (b+loss) :=
    mul_pos (mul_pos (mul_pos heb hb) hN) (exposure_pos h (b+loss) hh hg)
  intro i
  fin_cases i
  · simpa [means] using add_pos_of_pos_of_nonneg ha (hB 0)
  · simpa [means] using add_pos_of_pos_of_nonneg (mul_pos ha hu) (hB 1)
  · simpa [means] using add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos hes hN) (sq_pos_of_pos hu)) (hB 2)

theorem identifiable_fisher (eb es h b loss N : ℝ) (B : Fin 3 → ℝ)
    (heb : 0 < eb) (hes : 0 < es) (hh : 0 < h) (hb : 0 < b)
    (hl : 0 ≤ loss) (hN : 0 < N) (hB : ∀ i, 0 ≤ B i) :
    (fisher (jacobian eb es h b loss N) (means eb es h b loss N B)).PosDef ∧
      0 < (fisher (jacobian eb es h b loss N) (means eb es h b loss N B)).det := by
  have hg : 0 < b+loss := by linarith
  have hu := (survival_bounds h (b+loss) hh hg).1
  have ha := exposure_pos h (b+loss) hh hg
  have hj : (jacobian eb es h b loss N).det ≠ 0 := by
    rw [jacobian_det]
    exact ne_of_lt (neg_neg_of_pos (by positivity))
  have hm := means_pos eb es h b loss N B heb hes hh hb hl hN hB
  refine ⟨fisher_posDef _ _ hj hm, ?_⟩
  rw [fisher_det]
  exact mul_pos (sq_pos_of_ne_zero hj) (Finset.prod_pos fun i _ => inv_pos.mpr (hm i))

theorem zero_beta_efficiency (es h b loss N : ℝ) (B : Fin 3 → ℝ) :
    (fisher (jacobian 0 es h b loss N) (means 0 es h b loss N B)).det = 0 := by
  rw [fisher_det, jacobian_det]
  simp

/-- Algebraic invariance, including both beta bins and the terminal channel. -/
theorem unknown_efficiency_confounding (eb es h b loss N q : ℝ) (hq : q ≠ 0)
    (B : Fin 3 → ℝ) :
    means (eb/q) es h (q*b) (loss+(1-q)*b) N B = means eb es h b loss N B := by
  have hg : q*b+(loss+(1-q)*b) = b+loss := by ring
  simp only [means, hg, amplitude]
  have he : eb/q*(q*b) = eb*b := by field_simp
  rw [he]

/-- Explicit recovery of the three parameters from noiseless means after background
subtraction. This is structural identifiability, not finite-sample precision. -/
theorem recovery (eb es h b loss N : ℝ) (B : Fin 3 → ℝ)
    (heb : 0 < eb) (hes : 0 < es) (hh : 0 < h) (hb : 0 < b)
    (hl : 0 ≤ loss) (hN : 0 < N) :
    let mu := means eb es h b loss N B
    let u := (mu 1 - B 1) / (mu 0 - B 0)
    (-Real.log u / h = b + loss) ∧
    ((mu 2 - B 2) / (es * u^2) = N) ∧
    ((mu 0 - B 0) / (eb * N * exposure h (b+loss)) = b) := by
  have hg : 0 < b+loss := by linarith
  have hu : survival h (b+loss) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have ha : exposure h (b+loss) ≠ 0 := ne_of_gt (exposure_pos h (b+loss) hh hg)
  have hA : amplitude eb b N h (b+loss) ≠ 0 := by
    unfold amplitude
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero heb.ne' hb.ne') hN.ne') ha
  dsimp only
  have hr : (means eb es h b loss N B 1 - B 1) /
      (means eb es h b loss N B 0 - B 0) = survival h (b+loss) := by
    simp [means, mul_div_cancel_left₀, hA]
  rw [hr]
  refine ⟨?_, ?_, ?_⟩
  · simp only [survival, Real.log_exp]
    field_simp
  · simp [means]
    field_simp
  · simp [means, amplitude]
    field_simp

structure PrometheusLifetimeIdentifiabilitySuite : Prop where
  positive : ∀ eb es h b loss N B, 0 < eb → 0 < es → 0 < h → 0 < b →
    0 ≤ loss → 0 < N → (∀ i, 0 ≤ B i) →
    (fisher (jacobian eb es h b loss N) (means eb es h b loss N B)).PosDef ∧
    0 < (fisher (jacobian eb es h b loss N) (means eb es h b loss N B)).det
  degeneracy : ∀ es h b loss N B,
    (fisher (jacobian 0 es h b loss N) (means 0 es h b loss N B)).det = 0

theorem verification_suite : PrometheusLifetimeIdentifiabilitySuite :=
  ⟨identifiable_fisher, zero_beta_efficiency⟩
end
end PrometheusLifetimeIdentifiability

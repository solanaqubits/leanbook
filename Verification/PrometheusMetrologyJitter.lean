/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PrometheusChannelAndInjectorAudit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Conditional matter-action, calibration and timing covariance

The integral is a scalar matter-potential contribution, not the full generally
noncommuting MSW flavor propagator, an arrival delay, or a pointing law. The finite
quadrature covariance theorem is separate from the continuous deterministic bound;
no quadrature convergence or measured material model is inferred. Timing response
requires an explicit calibrated map. Source kinetic energy is not instantaneous
scintillation light. All stochastic statements below use a normalized finite law.
-/
namespace PrometheusMetrologyJitter
noncomputable section
open scoped BigOperators
open MeasureTheory

/-- Consistent units and deterministic density/composition profiles are supplied. -/
def electronDensity (avogadro : ℝ) (density electronFraction : ℝ → ℝ) (x : ℝ) : ℝ :=
  density x * avogadro * electronFraction x

def matterPhase (kappa avogadro length : ℝ) (density perturbation : ℝ → ℝ) : ℝ :=
  (kappa * avogadro) * ∫ x in 0..length, density x * perturbation x

theorem matter_phase_add (kappa avogadro length : ℝ) (density u v : ℝ → ℝ)
    (hu : IntervalIntegrable (fun x => density x * u x) volume 0 length)
    (hv : IntervalIntegrable (fun x => density x * v x) volume 0 length) :
    matterPhase kappa avogadro length density (fun x => u x + v x) =
      matterPhase kappa avogadro length density u +
        matterPhase kappa avogadro length density v := by
  unfold matterPhase
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add hu hv]
  ring

/-- The integrability premise rules out interpreting Lean's total integral fallback. -/
theorem continuous_phase_bound (kappa avogadro length rhoMax epsilon : ℝ)
    (density perturbation : ℝ → ℝ) (hL : 0 ≤ length) (hrho : 0 ≤ rhoMax)
    (_hInt : IntervalIntegrable (fun x => density x * perturbation x) volume 0 length)
    (hr : ∀ x ∈ Set.uIoc 0 length, |density x| ≤ rhoMax)
    (he : ∀ x ∈ Set.uIoc 0 length, |perturbation x| ≤ epsilon) :
    |matterPhase kappa avogadro length density perturbation| ≤
      |kappa * avogadro| * (rhoMax * epsilon * length) := by
  have hi : |∫ x in 0..length, density x * perturbation x| ≤ rhoMax * epsilon * length := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x => density x * perturbation x) (C := rhoMax * epsilon) (a := 0) (b := length)
      (fun x hx => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hr x hx) (he x hx) (abs_nonneg _) hrho)
    simpa [Real.norm_eq_abs, abs_of_nonneg hL] using h
  simpa [matterPhase, abs_mul] using mul_le_mul_of_nonneg_left hi (abs_nonneg (kappa * avogadro))

/-- The same composition change has a density-dependent action. -/
theorem density_scaling (kappa avogadro length scale : ℝ) (density u : ℝ → ℝ) :
    matterPhase kappa avogadro length (fun x => scale * density x) u =
      scale * matterPhase kappa avogadro length density u := by
  unfold matterPhase
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonnegative : ∀ ω, 0 ≤ mass ω
  normalized : ∑ ω, mass ω = 1

variable {Ω : Type*} [Fintype Ω]

def mean (law : FiniteLaw Ω) (X : Ω → ℝ) : ℝ := ∑ ω, law.mass ω * X ω

def centered (law : FiniteLaw Ω) (X : Ω → ℝ) (ω : Ω) : ℝ := X ω - mean law X

def covariance (law : FiniteLaw Ω) (X Y : Ω → ℝ) : ℝ :=
  ∑ ω, law.mass ω * (centered law X ω * centered law Y ω)

def variance (law : FiniteLaw Ω) (X : Ω → ℝ) : ℝ := covariance law X X

theorem mean_add (law : FiniteLaw Ω) (X Y : Ω → ℝ) :
    mean law (fun ω => X ω + Y ω) = mean law X + mean law Y := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_scale (law : FiniteLaw Ω) (a : ℝ) (X : Ω → ℝ) :
    mean law (fun ω => a * X ω) = a * mean law X := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem mean_const (law : FiniteLaw Ω) (a : ℝ) : mean law (fun _ => a) = a := by
  simp [mean, ← Finset.sum_mul, law.normalized]

theorem mean_sum {ι : Type*} [Fintype ι] (law : FiniteLaw Ω) (X : ι → Ω → ℝ) :
    mean law (fun ω => ∑ i, X i ω) = ∑ i, mean law (X i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem centered_add (law : FiniteLaw Ω) (X Y : Ω → ℝ) (ω : Ω) :
    centered law (fun ω => X ω + Y ω) ω = centered law X ω + centered law Y ω := by
  simp only [centered, mean_add]
  ring

theorem centered_scale (law : FiniteLaw Ω) (a : ℝ) (X : Ω → ℝ) (ω : Ω) :
    centered law (fun ω => a * X ω) ω = a * centered law X ω := by
  simp only [centered, mean_scale]
  ring

theorem centered_sum {ι : Type*} [Fintype ι] (law : FiniteLaw Ω)
    (X : ι → Ω → ℝ) (ω : Ω) :
    centered law (fun ω => ∑ i, X i ω) ω = ∑ i, centered law (X i) ω := by
  simp only [centered, mean_sum, Finset.sum_sub_distrib]

theorem covariance_comm (law : FiniteLaw Ω) (X Y : Ω → ℝ) :
    covariance law X Y = covariance law Y X := by
  simp only [covariance, mul_comm (centered law X _) (centered law Y _)]

theorem covariance_add_left (law : FiniteLaw Ω) (X Y Z : Ω → ℝ) :
    covariance law (fun ω => X ω + Y ω) Z = covariance law X Z + covariance law Y Z := by
  simp [covariance, centered_add, add_mul, mul_add, Finset.sum_add_distrib]

theorem covariance_add_right (law : FiniteLaw Ω) (X Y Z : Ω → ℝ) :
    covariance law X (fun ω => Y ω + Z ω) = covariance law X Y + covariance law X Z := by
  rw [covariance_comm, covariance_add_left, covariance_comm law Y X,
    covariance_comm law Z X]

theorem covariance_scale_left (law : FiniteLaw Ω) (a : ℝ) (X Y : Ω → ℝ) :
    covariance law (fun ω => a * X ω) Y = a * covariance law X Y := by
  simp only [covariance, centered_scale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem covariance_scale_right (law : FiniteLaw Ω) (a : ℝ) (X Y : Ω → ℝ) :
    covariance law X (fun ω => a * Y ω) = a * covariance law X Y := by
  rw [covariance_comm, covariance_scale_left, covariance_comm law Y X]

theorem covariance_sum_left {ι : Type*} [Fintype ι] (law : FiniteLaw Ω)
    (X : ι → Ω → ℝ) (Y : Ω → ℝ) :
    covariance law (fun ω => ∑ i, X i ω) Y = ∑ i, covariance law (X i) Y := by
  simp only [covariance, centered_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem covariance_sum_right {ι : Type*} [Fintype ι] (law : FiniteLaw Ω)
    (X : Ω → ℝ) (Y : ι → Ω → ℝ) :
    covariance law X (fun ω => ∑ i, Y i ω) = ∑ i, covariance law X (Y i) := by
  rw [covariance_comm, covariance_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact covariance_comm law (Y i) X

theorem variance_nonnegative (law : FiniteLaw Ω) (X : Ω → ℝ) : 0 ≤ variance law X := by
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (law.nonnegative ω) (mul_self_nonneg _)

/-- Actual centered covariance of a finite quadrature, including all off-diagonal terms. -/
theorem variance_linear_functional {ι : Type*} [Fintype ι]
    (law : FiniteLaw Ω) (weights : ι → ℝ) (X : ι → Ω → ℝ) :
    variance law (fun ω => ∑ i, weights i * X i ω) =
      ∑ i, ∑ j, weights i * weights j * covariance law (X i) (X j) := by
  unfold variance
  rw [covariance_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [covariance_sum_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [covariance_scale_left, covariance_scale_right]
  ring

/-- Width and density are part of the weights; composition alone is insufficient. -/
def phaseWeight {ι : Type*} (kappa avogadro : ℝ) (width density : ι → ℝ) (i : ι) : ℝ :=
  kappa * avogadro * width i * density i

def quadraturePhase {ι : Type*} [Fintype ι] (kappa avogadro : ℝ)
    (width density : ι → ℝ) (deltaYe : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ i, phaseWeight kappa avogadro width density i * deltaYe i ω

theorem quadrature_covariance {ι : Type*} [Fintype ι] (law : FiniteLaw Ω)
    (kappa avogadro : ℝ) (width density : ι → ℝ) (deltaYe : ι → Ω → ℝ) :
    variance law (quadraturePhase kappa avogadro width density deltaYe) =
      ∑ i, ∑ j, phaseWeight kappa avogadro width density i *
        phaseWeight kappa avogadro width density j * covariance law (deltaYe i) (deltaYe j) :=
  variance_linear_functional law _ _

theorem variance_scale (law : FiniteLaw Ω) (gain : ℝ) (X : Ω → ℝ) :
    variance law (fun ω => gain * X ω) = gain ^ 2 * variance law X := by
  unfold variance
  rw [covariance_scale_left, covariance_scale_right]
  ring

/-- Exact finite-law variance of the actual continuous integral, without a Fubini claim. -/
theorem continuous_phase_variance (law : FiniteLaw Ω) (kappa avogadro length : ℝ)
    (density : ℝ → ℝ) (deltaYe : Ω → ℝ → ℝ)
    (_hInt : ∀ ω, IntervalIntegrable (fun x => density x * deltaYe ω x) volume 0 length) :
    variance law (fun ω => matterPhase kappa avogadro length density (deltaYe ω)) =
      (kappa * avogadro) ^ 2 *
        variance law (fun ω => ∫ x in 0..length, density x * deltaYe ω x) :=
  variance_scale law (kappa * avogadro) _

theorem variance_add (law : FiniteLaw Ω) (X Y : Ω → ℝ) :
    variance law (fun ω => X ω + Y ω) =
      variance law X + variance law Y + 2 * covariance law X Y := by
  unfold variance
  rw [covariance_add_left, covariance_add_right, covariance_add_right,
    covariance_comm law Y X]
  ring

theorem variance_difference (law : FiniteLaw Ω) (X Y : Ω → ℝ) :
    variance law (fun ω => X ω - Y ω) =
      variance law X + variance law Y - 2 * covariance law X Y := by
  have he : (fun ω => X ω - Y ω) = (fun ω => X ω + (-1) * Y ω) := by funext ω; ring
  rw [he, variance_add, variance_scale, covariance_scale_right]
  ring

theorem common_mode_cancels (law : FiniteLaw Ω) (X Y common : Ω → ℝ) :
    variance law (fun ω => (X ω + common ω) - (Y ω + common ω)) =
      variance law (fun ω => X ω - Y ω) := by
  congr 1
  funext ω
  ring

theorem variance_uncorrelated_sum {ι : Type*} [Fintype ι]
    (law : FiniteLaw Ω) (weights : ι → ℝ) (X : ι → Ω → ℝ)
    (hcov : ∀ i j, i ≠ j → covariance law (X i) (X j) = 0) :
    variance law (fun ω => ∑ i, weights i * X i ω) =
      ∑ i, weights i ^ 2 * variance law (X i) := by
  classical
  rw [variance_linear_functional]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · unfold variance
    ring
  · intro j _ hj
    rw [hcov i j (Ne.symm hj)]
    ring
  · simp

/-- Fixed positive detected photon count; the conditional law may depend on this count. -/
def photonAverage (count : ℕ) (X : Fin count → Ω → ℝ) (ω : Ω) : ℝ :=
  (1 / (count : ℝ)) * ∑ i, X i ω

theorem photon_average_variance (law : FiniteLaw Ω) (count : ℕ) (hc : 0 < count)
    (X : Fin count → Ω → ℝ) (photonVariance : ℝ)
    (hvar : ∀ i, variance law (X i) = photonVariance)
    (hcov : ∀ i j, i ≠ j → covariance law (X i) (X j) = 0) :
    variance law (photonAverage count X) = photonVariance / count := by
  have h := variance_uncorrelated_sum law (fun _ : Fin count => 1 / (count : ℝ)) X hcov
  simp only [← Finset.mul_sum] at h
  change variance law (photonAverage count X) = _ at h
  simp_rw [hvar] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [h]
  have hn : (count : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  field_simp

/-- Independent photon jitter averages down; shared onset jitter is not divided by count. -/
theorem sample_mean_with_shared_variance (law : FiniteLaw Ω) (count : ℕ)
    (hc : 0 < count) (X : Fin count → Ω → ℝ) (shared : Ω → ℝ) (photonVariance : ℝ)
    (hvar : ∀ i, variance law (X i) = photonVariance)
    (hcov : ∀ i j, i ≠ j → covariance law (X i) (X j) = 0)
    (hshared : ∀ i, covariance law (X i) shared = 0) :
    variance law (fun ω => photonAverage count X ω + shared ω) =
      photonVariance / count + variance law shared := by
  rw [variance_add, photon_average_variance law count hc X photonVariance hvar hcov]
  have hz : covariance law (photonAverage count X) shared = 0 := by
    unfold photonAverage
    rw [covariance_scale_left, covariance_sum_left]
    simp [hshared]
  rw [hz]
  ring

/-- Removing a stipulated response mean removes this bias, not unmodeled calibration error. -/
theorem calibrated_photon_mean (law : FiniteLaw Ω) (count : ℕ) (hc : 0 < count)
    (X : Fin count → Ω → ℝ) (responseMean : ℝ)
    (hmean : ∀ i, mean law (X i) = responseMean) :
    mean law (fun ω => photonAverage count X ω - responseMean) = 0 := by
  have hfun : (fun ω => photonAverage count X ω - responseMean) =
      (fun ω => photonAverage count X ω + (-responseMean)) := by funext ω; ring
  rw [hfun, mean_add, mean_const]
  unfold photonAverage
  rw [mean_scale, mean_sum]
  simp_rw [hmean]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (count : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  field_simp
  ring

/-- A calibration hypothesis, not a consequence of the matter potential. -/
def CalibratedBound (response : ℝ → ℝ) (gain : ℝ) : Prop :=
  ∀ x y, |response x - response y| ≤ gain * |x - y|

theorem linear_response_calibrated (offset gain : ℝ) :
    CalibratedBound (fun x => offset + gain * x) |gain| := by
  intro x y
  have he : (offset + gain * x) - (offset + gain * y) = gain * (x - y) := by ring
  rw [he, abs_mul]

theorem calibrated_error_bound (response : ℝ → ℝ) (gain epsilon x y : ℝ)
    (h : CalibratedBound response gain) (hg : 0 ≤ gain) (he : |x - y| ≤ epsilon) :
    |response x - response y| ≤ gain * epsilon :=
  (h x y).trans (mul_le_mul_of_nonneg_left he hg)

theorem continuous_calibrated_error_bound (response : ℝ → ℝ)
    (gain kappa avogadro length rhoMax epsilon : ℝ) (density perturbation : ℝ → ℝ)
    (hcal : CalibratedBound response gain) (hg : 0 ≤ gain)
    (hL : 0 ≤ length) (hrho : 0 ≤ rhoMax)
    (hInt : IntervalIntegrable (fun x => density x * perturbation x) volume 0 length)
    (hr : ∀ x ∈ Set.uIoc 0 length, |density x| ≤ rhoMax)
    (he : ∀ x ∈ Set.uIoc 0 length, |perturbation x| ≤ epsilon) :
    |response (matterPhase kappa avogadro length density perturbation) - response 0| ≤
      gain * (|kappa * avogadro| * (rhoMax * epsilon * length)) := by
  apply calibrated_error_bound response gain _ _ 0 hcal hg
  simpa using continuous_phase_bound kappa avogadro length rhoMax epsilon
    density perturbation hL hrho hInt hr he

theorem zero_gain_nonidentifiable (offset x y : ℝ) : offset + 0 * x = offset + 0 * y := by
  ring

/-- Scalar phase equivalence; this does not define an experimental phase estimator. -/
def PhaseEquivalent (period x y : ℝ) : Prop := ∃ k : ℤ, x - y = (k : ℝ) * period

theorem period_alias (period x : ℝ) : PhaseEquivalent period x (x + period) := by
  refine ⟨-1, ?_⟩
  push_cast
  ring

/-- A known branch separation <period makes unwrapping unique. -/
theorem unwrap_unique (period x y : ℝ) (hp : 0 < period)
    (h : PhaseEquivalent period x y) (hbranch : |x - y| < period) : x = y := by
  obtain ⟨k, hk⟩ := h
  rw [hk, abs_mul, abs_of_pos hp] at hbranch
  have habs : |(k : ℝ)| < 1 := by nlinarith
  have hkint : |k| < (1 : ℤ) := by exact_mod_cast habs
  have hkbounds := abs_lt.mp hkint
  have hkzero : k = 0 := by omega
  simp [hkzero] at hk
  linarith

/-- A scalar calibration factor can be zero even when phase representatives differ. -/
theorem phase_alias_distinct (period x : ℝ) (hp : 0 < period) :
    PhaseEquivalent period x (x + period) ∧ x ≠ x + period := by
  exact ⟨period_alias period x, by linarith⟩

/-- A zero-photon observation yields no estimate, avoiding division by zero as an estimator. -/
def sampleTimestamp (count : ℕ) (sumOfTimes : ℝ) : Option ℝ :=
  if count = 0 then none else some (sumOfTimes / count)

theorem no_photon_no_timestamp (sumOfTimes : ℝ) : sampleTimestamp 0 sumOfTimes = none := rfl

theorem positive_photon_timestamp (count : ℕ) (hc : 0 < count) (sumOfTimes : ℝ) :
    sampleTimestamp count sumOfTimes = some (sumOfTimes / count) := by
  simp [sampleTimestamp, Nat.ne_of_gt hc]

/-- The reused exact neutron kinetic yield is an energy identity, not an optical flash law. -/
theorem source_energy_only :
    PrometheusChannelAndInjectorAudit.injectorNeutronKineticJ = 117759982599 / 100000000000000000 :=
  PrometheusChannelAndInjectorAudit.neutron_kinetic_exact

structure PrometheusMetrologyJitterSuite : Prop where
  nonnegative : ∀ (Ω : Type) [Fintype Ω] (law : FiniteLaw Ω) X, 0 ≤ variance law X
  variance_response : ∀ (Ω : Type) [Fintype Ω] (law : FiniteLaw Ω) gain X,
    variance law (fun ω => gain * X ω) = gain ^ 2 * variance law X
  difference : ∀ (Ω : Type) [Fintype Ω] (law : FiniteLaw Ω) X Y,
    variance law (fun ω => X ω - Y ω) =
      variance law X + variance law Y - 2 * covariance law X Y
  unwrap : ∀ period x y, 0 < period → PhaseEquivalent period x y →
    |x - y| < period → x = y

theorem verification_suite : PrometheusMetrologyJitterSuite :=
  ⟨fun _ _ => variance_nonnegative, fun _ _ => variance_scale,
    fun _ _ => variance_difference, unwrap_unique⟩
end
end PrometheusMetrologyJitter

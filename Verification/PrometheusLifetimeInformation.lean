/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PrometheusMetrologyJitter

/-!
# Conditional calibration yield and lifetime information

Finite-law score covariance identities are explicit assumptions. These theorems do
not derive regularity, unbiasedness, asymptotic normality, or interval coverage of
an MLE, nor a quantum/physical lower bound. Photon response and detection efficiencies
are supplied independently of neutron kinetic energy. Unknown storage losses prevent
identifying the beta lifetime from the disappearance rate alone.
-/
namespace PrometheusLifetimeInformation
open PrometheusMetrologyJitter
noncomputable section

/-- All fractions and photon yield must be calibrated separately. No beta efficiency
is inferred from this optical count expectation. Light yield is photons per joule. -/
def expectedPhotoelectrons (energy geometry deposition lightYield transport pde : ℝ) : ℝ :=
  energy * geometry * deposition * lightYield * transport * pde

theorem energy_chain_nonnegative (energy geometry deposition lightYield transport pde : ℝ)
    (he : 0 ≤ energy) (hg : 0 ≤ geometry) (hd : 0 ≤ deposition)
    (hl : 0 ≤ lightYield) (ht : 0 ≤ transport) (hp : 0 ≤ pde) :
    0 ≤ expectedPhotoelectrons energy geometry deposition lightYield transport pde :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg he hg) hd) hl) ht) hp

theorem zero_acceptance_no_expected_photons (energy deposition lightYield transport pde : ℝ) :
    expectedPhotoelectrons energy 0 deposition lightYield transport pde = 0 := by
  simp [expectedPhotoelectrons]

/-- Two hypothetical detectors with the same positive source energy disagree on
expected detected photons. This is a model counterexample, not measured yields. -/
theorem same_energy_different_counts (energy : ℝ) (he : 0 < energy) :
    expectedPhotoelectrons energy 0 1 1 1 1 = 0 ∧
    expectedPhotoelectrons energy 1 1 1 1 1 = energy ∧
    expectedPhotoelectrons energy 0 1 1 1 1 ≠ expectedPhotoelectrons energy 1 1 1 1 1 := by
  simp [expectedPhotoelectrons, Ne.symm (ne_of_gt he)]

/-- Mean-yield energy arithmetic supplies neither a realized count nor a timestamp. -/
theorem positive_energy_without_timestamp :
    0 < PrometheusChannelAndInjectorAudit.injectorNeutronKineticJ ∧
    expectedPhotoelectrons PrometheusChannelAndInjectorAudit.injectorNeutronKineticJ
      0 1 1 1 1 = 0 ∧ sampleTimestamp 0 0 = none := by
  rw [source_energy_only]
  norm_num [expectedPhotoelectrons, sampleTimestamp]

/-- Conditional variance budget; zero count is explicitly not an estimate. -/
def timestampVariance (count : ℕ) (singlePhoton shared : ℝ) : Option ℝ :=
  if count = 0 then none else some (singlePhoton / count + shared)

theorem equal_count_different_precision :
    timestampVariance 1 1 0 = some 1 ∧ timestampVariance 1 4 0 = some 4 ∧
      timestampVariance 0 1 0 = none := by norm_num [timestampVariance]

theorem shared_floor (count : ℕ) (hc : 0 < count) (singlePhoton shared : ℝ)
    (hs : 0 ≤ singlePhoton) : shared ≤ singlePhoton / count + shared := by
  have hn : (0 : ℝ) < count := by exact_mod_cast hc
  have h := div_nonneg hs (le_of_lt hn)
  linarith

variable {Ω : Type*} [Fintype Ω]

/-- Finite-law covariance algebra. `cov(error,score)=1` is the substantive score
identity required by an unbiased regular parametric model; it is NOT proved here.
A zero score mean is explicit so variance(score) has the usual information meaning. -/
theorem score_information_bound (law : FiniteLaw Ω) (error score : Ω → ℝ)
    (_hmean : mean law score = 0) (hcov : covariance law error score = 1)
    (hinfo : 0 < variance law score) :
    1 / variance law score ≤ variance law error := by
  let I := variance law score
  have hI : 0 < I := hinfo
  have hn := variance_nonnegative law (fun ω => error ω - (1 / I) * score ω)
  rw [variance_difference, variance_scale, covariance_scale_right, hcov] at hn
  change 0 ≤ variance law error + (1 / I) ^ 2 * I - 2 * (1 / I * 1) at hn
  have hid : (1 / I) ^ 2 * I = 1 / I := by field_simp
  rw [hid] at hn
  linarith

/-- Zero information cannot satisfy the unit score covariance identity. -/
theorem zero_information_no_unit_identity (law : FiniteLaw Ω) (error score : Ω → ℝ)
    (hi : variance law score = 0) : covariance law error score ≠ 1 := by
  intro hc
  have hn := variance_nonnegative law
    (fun ω => error ω - (variance law error + 1) * score ω)
  rw [variance_difference, variance_scale, covariance_scale_right, hi, hc] at hn
  have hv := variance_nonnegative law error
  nlinarith

/-- A scalar nuisance score is projected out. Orthogonality to the nuisance is an
explicit estimator assumption; no matrix invertibility or fitted-MLE claim is hidden. -/
def residualScore (score nuisance : Ω → ℝ) (coefficient : ℝ) : Ω → ℝ :=
  fun ω => score ω - coefficient * nuisance ω

theorem residual_covariance (law : FiniteLaw Ω) (error score nuisance : Ω → ℝ)
    (coefficient : ℝ) (hs : covariance law error score = 1)
    (hn : covariance law error nuisance = 0) :
    covariance law error (residualScore score nuisance coefficient) = 1 := by
  have he : residualScore score nuisance coefficient =
      (fun ω => score ω + (-coefficient) * nuisance ω) := by
    funext ω
    simp only [residualScore]
    ring
  rw [he, covariance_add_right, covariance_scale_right, hs, hn]
  ring

theorem residual_mean (law : FiniteLaw Ω) (score nuisance : Ω → ℝ)
    (coefficient : ℝ) (hs : mean law score = 0) (hn : mean law nuisance = 0) :
    mean law (residualScore score nuisance coefficient) = 0 := by
  have he : residualScore score nuisance coefficient =
      (fun ω => score ω + (-coefficient) * nuisance ω) := by
    funext ω
    simp only [residualScore]
    ring
  rw [he, mean_add, mean_scale, hs, hn]
  ring

theorem nuisance_information_bound (law : FiniteLaw Ω) (error score nuisance : Ω → ℝ)
    (coefficient : ℝ) (hsmean : mean law score = 0) (hnmean : mean law nuisance = 0)
    (hs : covariance law error score = 1) (hn : covariance law error nuisance = 0)
    (hi : 0 < variance law (residualScore score nuisance coefficient)) :
    1 / variance law (residualScore score nuisance coefficient) ≤ variance law error :=
  score_information_bound law error _ (residual_mean law score nuisance coefficient hsmean hnmean)
    (residual_covariance law error score nuisance coefficient hs hn) hi

/-- Exact scalar Schur-complement information under a positive nuisance variance. -/
theorem residual_information (law : FiniteLaw Ω) (score nuisance : Ω → ℝ)
    (hn : 0 < variance law nuisance) :
    variance law (residualScore score nuisance
      (covariance law score nuisance / variance law nuisance)) =
      variance law score - (covariance law score nuisance) ^ 2 / variance law nuisance := by
  unfold residualScore
  rw [variance_difference, variance_scale, covariance_scale_right]
  field_simp
  ring

/-- Estimating a nuisance cannot improve the projected scalar information. -/
theorem residual_information_le (law : FiniteLaw Ω) (score nuisance : Ω → ℝ)
    (hn : 0 < variance law nuisance) :
    variance law (residualScore score nuisance
      (covariance law score nuisance / variance law nuisance)) ≤ variance law score := by
  rw [residual_information law score nuisance hn]
  have h := div_nonneg (sq_nonneg (covariance law score nuisance)) (le_of_lt hn)
  linarith

/-- Disappearance combines beta decay and independently modeled storage losses. -/
def effectiveRate (betaLifetime lossRate : ℝ) : ℝ := 1 / betaLifetime + lossRate

theorem effective_rate_positive (betaLifetime lossRate : ℝ)
    (ht : 0 < betaLifetime) (hl : 0 ≤ lossRate) : 0 < effectiveRate betaLifetime lossRate := by
  unfold effectiveRate
  exact add_pos_of_pos_of_nonneg (one_div_pos.mpr ht) hl

/-- Positive lifetimes and nonnegative losses, yet identical disappearance rate. -/
theorem unknown_loss_nonidentifiable :
    effectiveRate 1 0 = effectiveRate 2 (1 / 2) ∧ (1 : ℝ) ≠ 2 := by
  norm_num [effectiveRate]

/-- An independently known loss rate restores identifiability on positive lifetimes. -/
theorem known_loss_identifiable (t₁ t₂ loss : ℝ) (h₁ : 0 < t₁) (h₂ : 0 < t₂)
    (h : effectiveRate t₁ loss = effectiveRate t₂ loss) : t₁ = t₂ := by
  have hi : 1 / t₁ = 1 / t₂ := by unfold effectiveRate at h; linarith
  field_simp at hi
  exact hi.symm

/-- Removing a calibrated loss rate recovers the inverse beta lifetime only. -/
theorem subtract_known_loss (betaLifetime loss : ℝ) :
    effectiveRate betaLifetime loss - loss = 1 / betaLifetime := by
  unfold effectiveRate
  ring

structure PrometheusLifetimeInformationSuite : Prop where
  no_timestamp : 0 < PrometheusChannelAndInjectorAudit.injectorNeutronKineticJ ∧
    expectedPhotoelectrons PrometheusChannelAndInjectorAudit.injectorNeutronKineticJ
      0 1 1 1 1 = 0 ∧ sampleTimestamp 0 0 = none
  information : ∀ (Ω : Type) [Fintype Ω] (law : FiniteLaw Ω) error score,
    mean law score = 0 → covariance law error score = 1 → 0 < variance law score →
      1 / variance law score ≤ variance law error
  nonidentifiable : effectiveRate 1 0 = effectiveRate 2 (1 / 2) ∧ (1 : ℝ) ≠ 2
  identified : ∀ t₁ t₂ loss, 0 < t₁ → 0 < t₂ →
    effectiveRate t₁ loss = effectiveRate t₂ loss → t₁ = t₂

theorem verification_suite : PrometheusLifetimeInformationSuite :=
  ⟨positive_energy_without_timestamp, fun _ _ => score_information_bound,
    unknown_loss_nonidentifiable, known_loss_identifiable⟩
end
end PrometheusLifetimeInformation

import Verification.PrometheusLifetimeInformation

open PrometheusLifetimeInformation PrometheusMetrologyJitter
noncomputable section
private def fairCoin : FiniteLaw Bool where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  normalized := by norm_num
private def sign (b : Bool) : ℝ := if b then 1 else -1
private theorem sign_variance : variance fairCoin sign = 1 := by
  norm_num [variance, covariance, centered, mean, fairCoin, sign, Fintype.sum_bool]
private theorem sign_mean : mean fairCoin sign = 0 := by
  norm_num [mean, fairCoin, sign, Fintype.sum_bool]
example : 1 / variance fairCoin sign ≤ variance fairCoin sign :=
  score_information_bound fairCoin sign sign sign_mean sign_variance (by rw [sign_variance]; norm_num)
example : variance fairCoin (fun _ => (0 : ℝ)) = 0 := by
  norm_num [variance, covariance, centered, mean, fairCoin, Fintype.sum_bool]
example : covariance fairCoin sign (fun _ => 0) ≠ 1 := by
  apply zero_information_no_unit_identity
  norm_num [variance, covariance, centered, mean, fairCoin, Fintype.sum_bool]
-- Merely positive information is insufficient without the unit covariance identity.
example : ¬ (1 / variance fairCoin sign ≤ variance fairCoin (fun _ => 0)) := by
  rw [sign_variance]
  norm_num [variance, covariance, centered, mean, fairCoin, Fintype.sum_bool]
example : variance fairCoin (residualScore sign sign 1) = 0 := by
  norm_num [variance, covariance, centered, mean, fairCoin, sign, residualScore, Fintype.sum_bool]
example : variance fairCoin (residualScore sign sign
    (covariance fairCoin sign sign / variance fairCoin sign)) =
    variance fairCoin sign - covariance fairCoin sign sign ^ 2 / variance fairCoin sign :=
  residual_information fairCoin sign sign (by rw [sign_variance]; norm_num)
example : variance fairCoin (residualScore sign sign
    (covariance fairCoin sign sign / variance fairCoin sign)) ≤ variance fairCoin sign :=
  residual_information_le fairCoin sign sign (by rw [sign_variance]; norm_num)
example : expectedPhotoelectrons 10 (1 / 2) (1 / 2) 100 (1 / 2) (1 / 2) = 125 / 2 := by
  norm_num [expectedPhotoelectrons]
example : expectedPhotoelectrons 10 0 1 1 1 1 = 0 ∧
    expectedPhotoelectrons 10 1 1 1 1 1 = 10 ∧
    expectedPhotoelectrons 10 0 1 1 1 1 ≠ expectedPhotoelectrons 10 1 1 1 1 1 :=
  same_energy_different_counts 10 (by norm_num)
example : timestampVariance 0 100 1 = none := rfl
example : timestampVariance 4 4 1 = some 2 := by norm_num [timestampVariance]
example : timestampVariance 4 16 1 = some 5 := by norm_num [timestampVariance]
example : (1 : ℝ) ≤ 4 / 1000000 + 1 := shared_floor 1000000 (by norm_num) 4 1 (by norm_num)
example : effectiveRate 877.75 0 = effectiveRate 1755.5 (1 / 1755.5) := by
  norm_num [effectiveRate]
example (t₁ t₂ loss : ℝ) (h₁ : 0 < t₁) (h₂ : 0 < t₂)
    (h : effectiveRate t₁ loss = effectiveRate t₂ loss) : t₁ = t₂ :=
  known_loss_identifiable t₁ t₂ loss h₁ h₂ h
example : ¬ (∀ t₁ t₂ loss₁ loss₂ : ℝ, 0 < t₁ → 0 < t₂ →
    effectiveRate t₁ loss₁ = effectiveRate t₂ loss₂ → t₁ = t₂) := by
  intro h
  have he := h 1 2 0 (1 / 2) (by norm_num) (by norm_num) unknown_loss_nonidentifiable.1
  norm_num at he

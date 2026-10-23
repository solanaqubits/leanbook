import Verification.PrometheusMetrologyJitter
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

open PrometheusMetrologyJitter
open scoped BigOperators
open MeasureTheory

noncomputable section

-- A finite, normalized, explicit reference probability space.
private def fairCoin : FiniteLaw Bool where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  normalized := by norm_num

private def sign (b : Bool) : ℝ := if b then 1 else -1

private theorem sign_variance : variance fairCoin sign = 1 := by
  norm_num [variance, covariance, centered, mean, fairCoin, sign, Fintype.sum_bool]

example : mean fairCoin sign = 0 := by
  norm_num [mean, fairCoin, sign, Fintype.sum_bool]
example : variance fairCoin sign = 1 := sign_variance
example : covariance fairCoin sign sign = 1 := sign_variance
example : variance fairCoin (fun ω => 5 * sign ω) = 25 := by
  rw [variance_scale, sign_variance]
  norm_num
example : variance fairCoin (fun ω => sign ω + sign ω) = 4 := by
  rw [variance_add, sign_variance]
  change 1 + 1 + 2 * variance fairCoin sign = 4
  rw [sign_variance]
  norm_num
example : variance fairCoin (fun ω => sign ω - sign ω) = 0 := by
  rw [variance_difference, sign_variance]
  change 1 + 1 - 2 * variance fairCoin sign = 0
  rw [sign_variance]
  norm_num
example : covariance fairCoin sign (fun ω => (-1) * sign ω) = -1 := by
  rw [covariance_scale_right]
  change (-1) * variance fairCoin sign = -1
  rw [sign_variance]
  norm_num
example : variance fairCoin (fun ω => sign ω - (-1) * sign ω) = 4 := by
  rw [variance_difference, variance_scale, covariance_scale_right, sign_variance]
  change 1 + (-1) ^ 2 * 1 - 2 * ((-1) * variance fairCoin sign) = 4
  rw [sign_variance]
  norm_num

-- Correlated coefficients require off-diagonal covariance terms.
example : variance fairCoin (fun ω => (2 * sign ω + 3 * sign ω)) = 25 := by
  have h : (fun ω => (2 * sign ω + 3 * sign ω)) = (fun ω => 5 * sign ω) := by
    funext ω
    ring
  rw [h, variance_scale, sign_variance]
  norm_num
example : (2 : ℝ) ^ 2 + 3 ^ 2 ≠ 25 := by norm_num
example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (w : Fin 3 → ℝ)
    (X : Fin 3 → Ω → ℝ) :
    variance law (fun ω => ∑ i, w i * X i ω) =
      ∑ i, ∑ j, w i * w j * covariance law (X i) (X j) :=
  variance_linear_functional law w X
example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (k N : ℝ)
    (width density : Fin 4 → ℝ) (X : Fin 4 → Ω → ℝ) :
    variance law (quadraturePhase k N width density X) =
      ∑ i, ∑ j, phaseWeight k N width density i * phaseWeight k N width density j *
        covariance law (X i) (X j) := quadrature_covariance law k N width density X
example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (X Y C : Ω → ℝ) :
    variance law (fun ω => (X ω + C ω) - (Y ω + C ω)) =
      variance law (fun ω => X ω - Y ω) := common_mode_cancels law X Y C
example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (X : Ω → ℝ) :
    0 ≤ variance law X := variance_nonnegative law X

-- Continuous action is separate from finite quadrature covariance and delay calibration.
example : electronDensity 3 (fun _ => 2) (fun _ => 1 / 2) 0 = 3 := by
  norm_num [electronDensity]
example : matterPhase 1 1 3 (fun _ => 2) (fun _ => 1 / 10) = 3 / 5 := by
  norm_num [matterPhase]
example : matterPhase 1 1 3 (fun _ => 4) (fun _ => 1 / 10) = 6 / 5 := by
  norm_num [matterPhase]
example (k N L scale : ℝ) (density X : ℝ → ℝ) :
    matterPhase k N L (fun x => scale * density x) X =
      scale * matterPhase k N L density X := density_scaling k N L scale density X
example (k N L R eps : ℝ) (density X : ℝ → ℝ) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hint : IntervalIntegrable (fun x => density x * X x) volume 0 L)
    (hr : ∀ x ∈ Set.uIoc 0 L, |density x| ≤ R)
    (he : ∀ x ∈ Set.uIoc 0 L, |X x| ≤ eps) :
    |matterPhase k N L density X| ≤ |k * N| * (R * eps * L) :=
  continuous_phase_bound k N L R eps density X hL hR hint hr he
example (density X : ℝ → ℝ) : matterPhase 0 7 9 density X = 0 := by simp [matterPhase]
example (k N : ℝ) (density X : ℝ → ℝ) : matterPhase k N 0 density X = 0 := by
  simp [matterPhase]

-- Explicit calibration and branch premises; modulo observations are not globally injective.
example (offset gain : ℝ) : CalibratedBound (fun x => offset + gain * x) |gain| :=
  linear_response_calibrated offset gain
example (response : ℝ → ℝ) (h : CalibratedBound response 2) (x y : ℝ)
    (he : |x - y| ≤ 1 / 10) : |response x - response y| ≤ 1 / 5 := by
  have hc := calibrated_error_bound response 2 (1 / 10) x y h (by norm_num) he
  norm_num at hc
  exact hc
example (offset : ℝ) : offset + 0 * (1 : ℝ) = offset + 0 * 2 :=
  zero_gain_nonidentifiable offset 1 2
example (x : ℝ) : PhaseEquivalent (2 * Real.pi) x (x + 2 * Real.pi) :=
  period_alias _ _
example (x : ℝ) : PhaseEquivalent (2 * Real.pi) x (x + 2 * Real.pi) ∧
    x ≠ x + 2 * Real.pi := phase_alias_distinct _ _ (by positivity)
example (x y : ℝ) (h : PhaseEquivalent (2 * Real.pi) x y) (hb : |x - y| < 2 * Real.pi) :
    x = y := unwrap_unique _ _ _ (by positivity) h hb
example : PhaseEquivalent 1 0 1 ∧ (0 : ℝ) ≠ 1 := by
  exact ⟨by simpa using period_alias 1 0, by norm_num⟩

-- Zero detected photons have no timestamp, not a fabricated zero-valued estimate.
example : sampleTimestamp 0 20 = none := no_photon_no_timestamp 20
example : sampleTimestamp 5 20 = some 4 := by norm_num [sampleTimestamp]
example (M : ℕ) (hM : 0 < M) (s : ℝ) : sampleTimestamp M s = some (s / M) :=
  positive_photon_timestamp M hM s
example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (M : ℕ) (hM : 0 < M)
    (X : Fin M → Ω → ℝ) (V : ℝ) (hv : ∀ i, variance law (X i) = V)
    (hc : ∀ i j, i ≠ j → covariance law (X i) (X j) = 0) :
    variance law (photonAverage M X) = V / M := photon_average_variance law M hM X V hv hc
example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (M : ℕ) (hM : 0 < M)
    (X : Fin M → Ω → ℝ) (shared : Ω → ℝ) (V : ℝ) (hv : ∀ i, variance law (X i) = V)
    (hc : ∀ i j, i ≠ j → covariance law (X i) (X j) = 0)
    (hs : ∀ i, covariance law (X i) shared = 0) :
    variance law (fun ω => photonAverage M X ω + shared ω) = V / M + variance law shared :=
  sample_mean_with_shared_variance law M hM X shared V hv hc hs
example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (M : ℕ) (hM : 0 < M)
    (X : Fin M → Ω → ℝ) (mu : ℝ) (hm : ∀ i, mean law (X i) = mu) :
    mean law (fun ω => photonAverage M X ω - mu) = 0 :=
  calibrated_photon_mean law M hM X mu hm
example : variance fairCoin (photonAverage 2 (fun _ => sign)) = 1 := by
  have he : photonAverage 2 (fun _ : Fin 2 => sign) = sign := by
    funext ω
    simp [photonAverage]
  rw [he, sign_variance]
example : (1 : ℝ) ≠ 1 / 2 := by norm_num
example : PrometheusChannelAndInjectorAudit.injectorNeutronKineticJ =
    117759982599 / 100000000000000000 := source_energy_only

example {Ω : Type} [Fintype Ω] (law : FiniteLaw Ω) (k N L : ℝ)
    (density : ℝ → ℝ) (X : Ω → ℝ → ℝ)
    (hint : ∀ ω, IntervalIntegrable (fun x => density x * X ω x) volume 0 L) :
    variance law (fun ω => matterPhase k N L density (X ω)) =
      (k * N) ^ 2 * variance law (fun ω => ∫ x in 0..L, density x * X ω x) :=
  continuous_phase_variance law k N L density X hint

-- Concrete independent two-photon witness, alongside the correlated counterexample above.
private def squareLaw : FiniteLaw (Fin 4) where
  mass _ := 1 / 4
  nonnegative _ := by norm_num
  normalized := by norm_num

private def photonPair : Fin 2 → Fin 4 → ℝ :=
  ![![1, 1, -1, -1], ![1, -1, 1, -1]]

example : covariance squareLaw (photonPair 0) (photonPair 1) = 0 := by
  norm_num [covariance, centered, mean, squareLaw, photonPair, Fin.sum_univ_succ]
example : variance squareLaw (photonAverage 2 photonPair) = 1 / 2 := by
  norm_num [variance, covariance, centered, mean, squareLaw, photonAverage, photonPair,
    Fin.sum_univ_succ]

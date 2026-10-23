/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.CDF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Relative jitter: identical common-mode coupling, L2 assumptions for Chebyshev,
and a separate joint-Gaussian premise for exact acceptance. No detector calibration.
-/
namespace PrometheusJitterWindow
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

def observation (t₀ delay : ℝ) (common noise : Ω → ℝ) (ω : Ω) : ℝ :=
  t₀ + delay + common ω + noise ω

def relative (t₀ dac drf : ℝ) (common ac rf : Ω → ℝ) : Ω → ℝ :=
  fun ω => observation t₀ dac common ac ω - observation t₀ drf common rf ω

omit [MeasurableSpace Ω] in
theorem common_cancellation (t₀ dac drf : ℝ) (common ac rf : Ω → ℝ) :
    relative t₀ dac drf common ac rf = fun ω => (dac - drf) + (ac ω - rf ω) := by
  funext ω
  simp only [relative, observation]
  ring

theorem relative_variance (t₀ dac drf : ℝ) (common ac rf : Ω → ℝ)
    (ha : MemLp ac 2 μ) (hr : MemLp rf 2 μ) :
    Var[relative t₀ dac drf common ac rf; μ] = Var[ac; μ] + Var[rf; μ] - 2 * cov[ac, rf; μ] := by
  rw [common_cancellation, variance_const_add (X := fun ω => ac ω - rf ω)
    (ha.sub hr).aestronglyMeasurable,
    variance_fun_sub ha hr]
  ring

theorem positive_covariance_reduction (t₀ dac drf : ℝ) (common ac rf : Ω → ℝ)
    (ha : MemLp ac 2 μ) (hr : MemLp rf 2 μ) (hc : 0 < cov[ac, rf; μ]) :
    Var[relative t₀ dac drf common ac rf; μ] < Var[ac; μ] + Var[rf; μ] := by
  rw [relative_variance t₀ dac drf common ac rf ha hr]
  linarith

theorem dropout_chebyshev (X : Ω → ℝ) (hX : MemLp X 2 μ) (w : ℝ) (hw : 0 < w) :
    μ {ω | w < |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / w ^ 2) := by
  have hsub : {ω | w < |X ω - μ[X]|} ⊆ {ω | w ≤ |X ω - μ[X]|} := by
    intro ω h
    exact le_of_lt (show w < |X ω - μ[X]| from h)
  exact (measure_mono hsub).trans (meas_ge_le_variance_div_sq hX hw)

theorem relative_chebyshev (t₀ dac drf : ℝ) (common ac rf : Ω → ℝ)
    (ha : MemLp ac 2 μ) (hr : MemLp rf 2 μ) (w : ℝ) (hw : 0 < w) :
    μ {ω | w < |relative t₀ dac drf common ac rf ω - μ[relative t₀ dac drf common ac rf]|}
      ≤ ENNReal.ofReal ((Var[ac; μ] + Var[rf; μ] - 2 * cov[ac, rf; μ]) / w ^ 2) := by
  have hm : MemLp (relative t₀ dac drf common ac rf) 2 μ := by
    rw [common_cancellation]
    exact (memLp_const (dac - drf)).add (ha.sub hr)
  simpa only [relative_variance t₀ dac drf common ac rf ha hr] using
    dropout_chebyshev _ hm w hw

/-- Without mean compensation the available margin is w - |mean|. -/
theorem biased_chebyshev (X : Ω → ℝ) (hX : MemLp X 2 μ) (w : ℝ) (hw : |μ[X]| < w) :
    μ {ω | w < |X ω|} ≤ ENNReal.ofReal (Var[X; μ] / (w - |μ[X]|) ^ 2) := by
  apply (measure_mono (show {ω | w < |X ω|} ⊆ {ω | w - |μ[X]| < |X ω - μ[X]|} from ?_)).trans
    (dropout_chebyshev X hX _ (sub_pos.mpr hw))
  intro ω h
  simp only [mem_ofPred_eq] at h ⊢
  have ht := abs_add_le (X ω - μ[X]) μ[X]
  rw [sub_add_cancel] at ht
  linarith

omit [IsProbabilityMeasure μ] in
/-- Explicit joint law; marginal Gaussianity alone would not suffice. -/
theorem joint_gaussian_difference (ac rf : Ω → ℝ)
    (h : HasGaussianLaw (fun ω => (ac ω, rf ω)) μ) :
    HasLaw (fun ω => ac ω - rf ω)
      (gaussianReal μ[fun ω => ac ω - rf ω] Var[fun ω => ac ω - rf ω; μ].toNNReal) μ :=
  ⟨h.fun_sub.aemeasurable, h.fun_sub.map_eq_gaussianReal⟩

/-- Standard normal CDF, defined by its probability measure. -/
def standardCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

lemma gaussian_interval (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1).real (Icc a b) = standardCDF b - standardCDF a := by
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have he : (gaussianReal 0 1) (Icc a b) = (gaussianReal 0 1) (Ioc a b) :=
    (measure_congr Ioc_ae_eq_Icc).symm
  unfold Measure.real
  rw [he, ← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf _ hab))]
  rfl

omit [IsProbabilityMeasure μ] in
/-- Nonzero Gaussian variance. A degenerate law is a Dirac measure, not a division by zero. -/
theorem gaussian_gate (X : Ω → ℝ) (m s w : ℝ) (hs : 0 < s) (hw : 0 ≤ w)
    (hX : HasLaw X (gaussianReal m (NNReal.mk (s ^ 2) (sq_nonneg s))) μ) :
    μ.real {ω | |X ω| ≤ w} = standardCDF ((w - m) / s) - standardCDF ((-w - m) / s) := by
  have hz0 := gaussianReal_div_const (gaussianReal_sub_const hX m) s
  have hv : ((NNReal.mk (s ^ 2) (sq_nonneg s)) : ℝ≥0) ≠ 0 := by
    intro he
    have he' : s ^ 2 = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
    nlinarith
  have hz : HasLaw (fun ω => (X ω - m) / s) (gaussianReal 0 1) μ := by
    have hd : ((NNReal.mk (s ^ 2) (sq_nonneg s)) : ℝ≥0) / NNReal.mk (s ^ 2) (sq_nonneg s) = 1 :=
      div_self hv
    rw [sub_self, zero_div, hd] at hz0
    exact hz0
  have he : {ω | |X ω| ≤ w} =
      {ω | (X ω - m) / s ∈ Icc ((-w - m) / s) ((w - m) / s)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_Icc, div_le_div_iff_of_pos_right hs, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [he]
  calc
    _ = (gaussianReal 0 1).real (Icc ((-w - m) / s) ((w - m) / s)) :=
      hz.measureReal_eq (p := fun x => x ∈ Icc ((-w - m) / s) ((w - m) / s)) measurableSet_Icc
    _ = _ := gaussian_interval _ _ ((div_le_div_iff_of_pos_right hs).mpr (by linarith))

omit [IsProbabilityMeasure μ] in
theorem joint_gaussian_gate (t₀ dac drf : ℝ) (common ac rf : Ω → ℝ)
    (h : HasGaussianLaw (fun ω => (ac ω, rf ω)) μ)
    (s w : ℝ) (hs : 0 < s) (hw : 0 ≤ w)
    (hv : Var[fun ω => ac ω - rf ω; μ] = s ^ 2) :
    μ.real {ω | |relative t₀ dac drf common ac rf ω - (dac - drf)| ≤ w} =
      standardCDF ((w - μ[fun ω => ac ω - rf ω]) / s) -
        standardCDF ((-w - μ[fun ω => ac ω - rf ω]) / s) := by
  have hn : Var[fun ω => ac ω - rf ω; μ].toNNReal = (NNReal.mk (s ^ 2) (sq_nonneg s)) := by
    ext
    change (Real.toNNReal _ : ℝ) = s ^ 2
    rw [hv, Real.coe_toNNReal _ (sq_nonneg s)]
  have hX := joint_gaussian_difference ac rf h
  rw [hn] at hX
  have he : (fun ω => relative t₀ dac drf common ac rf ω - (dac - drf)) =
      (fun ω => ac ω - rf ω) := by
    rw [common_cancellation]
    funext ω
    ring
  have hep (ω : Ω) := congrFun he ω
  simp only [hep]
  exact gaussian_gate (fun ω => ac ω - rf ω) _ s w hs hw hX

omit [IsProbabilityMeasure μ] in
theorem gaussian_zero_variance (X : Ω → ℝ) (m w : ℝ)
    (hX : HasLaw X (gaussianReal m 0) μ) :
    μ.real {ω | |X ω| ≤ w} = if |m| ≤ w then 1 else 0 := by
  have hset : MeasurableSet {x : ℝ | |x| ≤ w} :=
    measurableSet_le measurable_abs measurable_const
  rw [hX.measureReal_eq (p := fun x => |x| ≤ w) hset, gaussianReal_zero_var]
  by_cases h : |m| ≤ w <;> simp [Measure.real, h, Set.indicator_of_notMem]

structure PrometheusJitterWindowSuite : Prop where
  difference : ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∀ (t a b : ℝ) (c x y : ℝ → ℝ),
    MemLp x 2 ν → MemLp y 2 ν →
    Var[relative t a b c x y; ν] = Var[x; ν] + Var[y; ν] - 2 * cov[x, y; ν]
  chebyshev : ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∀ (x : ℝ → ℝ), MemLp x 2 ν →
    ∀ w : ℝ, 0 < w → ν {ω | w < |x ω - ν[x]|} ≤ ENNReal.ofReal (Var[x; ν] / w ^ 2)
  gaussian : ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ∀ (x : ℝ → ℝ) (m s w : ℝ),
    0 < s → 0 ≤ w → HasLaw x (gaussianReal m (NNReal.mk (s ^ 2) (sq_nonneg s))) ν →
    ν.real {ω | |x ω| ≤ w} = standardCDF ((w - m) / s) - standardCDF ((-w - m) / s)

theorem verification_suite : PrometheusJitterWindowSuite := by
  constructor
  · intro ν hν
    have : IsProbabilityMeasure ν := hν
    exact relative_variance
  · intro ν hν
    have : IsProbabilityMeasure ν := hν
    exact dropout_chebyshev
  · intro ν hν
    have : IsProbabilityMeasure ν := hν
    exact gaussian_gate

end
end PrometheusJitterWindow

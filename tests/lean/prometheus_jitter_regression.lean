import Verification.PrometheusJitterWindow
open MeasureTheory ProbabilityTheory PrometheusJitterWindow
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x y c : ℝ → ℝ)
    (hx : MemLp x 2 μ) (hy : MemLp y 2 μ) (hc : 0 < cov[x, y; μ]) :
    Var[relative 1 2 3 c x y; μ] < Var[x; μ] + Var[y; μ] :=
  positive_covariance_reduction 1 2 3 c x y hx hy hc
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ → ℝ) (hx : MemLp x 2 μ) :
    μ {ω | 250 < |x ω - μ[x]|} ≤ ENNReal.ofReal (Var[x;μ] / 250^2) :=
  dropout_chebyshev x hx 250 (by norm_num)
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ → ℝ)
    (hx : HasLaw x (gaussianReal 0 0) μ) : μ.real {ω | |x ω| ≤ 250} = 1 := by
  simpa using gaussian_zero_variance x 0 250 hx
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (x y c : ℝ → ℝ)
    (h : HasGaussianLaw (fun ω => (x ω, y ω)) μ)
    (hv : Var[fun ω => x ω - y ω; μ] = 200 ^ 2) :
    μ.real {ω | |relative 1 3 2 c x y ω - 1| ≤ 250} =
      standardCDF ((250-μ[fun ω => x ω - y ω])/200) -
      standardCDF ((-250-μ[fun ω => x ω - y ω])/200) := by
  simpa only [show (3 : ℝ) - 2 = 1 by norm_num] using joint_gaussian_gate 1 3 2 c x y h 200 250
    (by norm_num) (by norm_num) hv

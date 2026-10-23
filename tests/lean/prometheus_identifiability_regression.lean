import Verification.PrometheusLifetimeIdentifiability
open PrometheusLifetimeIdentifiability
example : (fisher (jacobian (2/5) (7/10) 500 (1/878) (1/1000) 10000)
    (means (2/5) (7/10) 500 (1/878) (1/1000) 10000 (fun _ => 1))).PosDef := by
  exact (identifiable_fisher _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => by norm_num)).1
example (b loss N : ℝ) :
    (fisher (jacobian 0 1 500 b loss N) (means 0 1 500 b loss N (fun _ => 1))).det = 0 :=
  zero_beta_efficiency _ _ _ _ _ _
example (eb es h b loss N : ℝ) (B : Fin 3 → ℝ) :
    means (eb/(1/2)) es h ((1/2)*b) (loss+(1-1/2)*b) N B =
      means eb es h b loss N B := unknown_efficiency_confounding _ _ _ _ _ _ _ (by norm_num) _
example (eb es h b loss N : ℝ) : (jacobian eb es h b loss N).det =
    -(eb^2*es*b*N^2*h*(survival h (b+loss))^3*(exposure h (b+loss))^2) :=
  jacobian_det _ _ _ _ _ _

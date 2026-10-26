import Verification.PrometheusNQKDFiniteKey
open PrometheusNQKDFiniteKey
example : bits (1 / 2) = 0 := half_bit_counterexample.2
example : bits 1 = 1 := by norm_num [bits]
example (q A : ℝ) : outputBits q A false true = 0 := abort_no_auth q A true
example (q A : ℝ) (h : 1 / 2 ≤ q) : outputBits q A true true = 0 := abort_phase q A true true h
example (n h L P : ℝ) (hn : 0 < n) : 0 < bits (budget n h L P) ↔ (L+P+1)/n ≤ 1-h
  := positive_rate_iff n h L P hn
example (a eps : ℝ) (ha : 0 < a) (he : 0 < eps) (he1 : eps ≤ 1) : Real.exp (-a * slack a eps ^ 2) =
  eps := tail_at_slack a eps ha he he1
example (H eps : ℝ) (he : 0 < eps) (h : 1 ≤ H - paPenalty eps) : hashResidual (bits (H - paPenalty
  eps)) H ≤ eps := integer_extraction_bound H eps he h
example : publicLeak 301 64 1 = 366 := historical_leak

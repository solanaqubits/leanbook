import Verification.PrometheusThresholdTomography
open PrometheusThresholdTomography
example : mutualInformation (atomicJoint 0) = 1 := by rw [atomic_information]; norm_num
example : mutualInformation (atomicJoint 3) = 0 := by rw [atomic_information]; norm_num
example : ¬ ConcaveOn ℝ Set.univ (fun t => mutualInformation (atomicJoint t)) := atomic_not_concave
example : ¬ ConvexOn ℝ Set.univ (fun t => mutualInformation (atomicJoint t)) := atomic_not_convex
example (r : Fin 16 → ℝ) : (duplicateColumns r).rank < 2 := duplicate_rank_lt_two r
example (A : Matrix (Fin 8) (Fin 4) ℝ) : (gram A).rank = A.rank := gram_rank A
example (A : Matrix (Fin 8) (Fin 4) ℝ) : identifiable A ↔ LinearMap.ker (gram A).mulVecLin = ⊥
  := identifiable_iff_gram_kernel A
example (f e p b c : ℝ) (hc : c ≠ 0) : countMean (f*c) (e/c) p b = countMean f e p b
  := flux_efficiency_gauge f e p b c hc
example (A : Matrix (Fin 2) (Fin 8) ℝ) : A.rank < 8 := insufficient_observations A (by norm_num)
example (ac rf delta w ta tr : ℝ) : ¬ trigger ac rf delta w ta tr false := dead_time_blocks ac rf
  delta w ta tr

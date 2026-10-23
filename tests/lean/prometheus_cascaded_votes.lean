import Verification.PrometheusCascadedFECBound
open PrometheusCascadedFECBound PrometheusFiniteBlockAudit

example : classify 0 = Noise.erased := rfl
example : classify (-1) = Noise.correct := rfl
example : classify 1 = Noise.flipped := rfl
example : fiveMass (atom 1 0 0) .erased = 1 := by
  rw [(five_mass_exact 1 0 0).1]; norm_num [tiePolynomial]
example : fiveMass (atom 0 1 0) .correct = 1 := by
  rw [(five_mass_exact 0 1 0).2.2]; norm_num [errorPolynomial]
example : fiveMass (atom 0 0 1) .flipped = 1 := by
  rw [(five_mass_exact 0 0 1).2.1]; norm_num [errorPolynomial]
example : byteMass (atom (1/2) (1/2) 0) .erased = 255/256 := by
  rw [byte_erasure _ (by rw [sum_noise]; norm_num [atom])]; norm_num [atom]
example : byteMass (atom 0 (1/2) (1/2)) .flipped = 255/256 := by
  rw [byte_error _ (by rw [sum_noise]; norm_num [atom])]; norm_num [atom]
example (n : ℕ) : weight (fun (_ : Fin n) => Noise.flipped) = 2*n := by
  simp [weight, cost]; omega
-- IID all-erased mass differs from a perfectly shared erasure event's mass.
example : (1/2 : ℚ)^5 ≠ 1/2 := by norm_num
example (sent : Bool) : decode (fun (_ : Fin 5) => observe sent Noise.erased) = none := by
  rw [observed_tie_erased]; simp [noiseScore, noiseExponent]

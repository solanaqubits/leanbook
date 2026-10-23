import Verification.PrometheusNQKDAudit

open PrometheusNQKDAudit QuantumBB84ProtocolQBER
open scoped BigOperators ComplexOrder

-- API applications, exact values, normalization and counterexamples.
example (b : BB84Basis) (x : BB84Bit) : (ket b x).conjTranspose * ket b x = 1 :=
  normalized_states b x
example : transition 0 1 0 1 = 1 / 2 := cross_basis_overlap 0 1
example : transition 0 0 0 1 = 0 := orthogonal_endpoint_counterexample.1
example : ¬ (0 < transition 0 0 0 1) := by rw [orthogonal_endpoint_counterexample.1]; norm_num
example : attackLaw.probability Sifted = 1 / 2 := born_intercept_quarter.1
example : attackLaw.probability (fun ω => Error ω ∧ Sifted ω) = 1 / 8 :=
  born_intercept_quarter.2.1
example : qber attackLaw = 1 / 4 := born_intercept_quarter.2.2
example : qber (partialLaw 0 (by norm_num) (by norm_num)) = 0 := by
  rw [partial_intercept_qber]; norm_num
example : qber (partialLaw 1 (by norm_num) (by norm_num)) = 1 / 4 := by
  rw [partial_intercept_qber]
example : qber (partialLaw (1/2) (by norm_num) (by norm_num)) = 1 / 8 := by
  rw [partial_intercept_qber]; norm_num
example : 0 < qber (partialLaw (1/2) (by norm_num) (by norm_num)) :=
  partial_interception_positive _ (by norm_num) (by norm_num)
example : noisyQber (partialLaw 1 (by norm_num) (by norm_num))
    (1/100) (by norm_num) (by norm_num) = 51 / 200 := by
  rw [independent_baseline_qber]; norm_num
example : noisyQber (partialLaw 0 (by norm_num) (by norm_num))
    (1/100) (by norm_num) (by norm_num) = 1 / 100 := by
  rw [independent_baseline_qber]; norm_num
example : noisyQber (partialLaw 1 (by norm_num) (by norm_num))
    (1/2) (by norm_num) (by norm_num) = 1 / 2 := by
  rw [independent_baseline_qber]; norm_num
-- Baseline p>1/2 reverses the direction; positive disturbance alone is not an increase.
example : noisyQber (partialLaw 1 (by norm_num) (by norm_num))
    1 (by norm_num) (by norm_num) = 3 / 4 := by
  rw [independent_baseline_qber]; norm_num
example : (noisyLaw attackLaw (1/100) (by norm_num) (by norm_num)).probability
    NoisySifted = 1 / 2 := by rw [noisy_sifting, sifting_probability_half]
example : ∑ ω, (noisyLaw attackLaw (1/100) (by norm_num) (by norm_num)).weight ω = 1 :=
  (noisyLaw attackLaw _ (by norm_num) (by norm_num)).normalized
example : 0 < (1 - (1 : ℝ) / 4)^10000 :=
  finite_iid_no_error_positive 1 (by norm_num) (by norm_num) _
example : (1 - (0 : ℝ) / 4)^10000 = 1 := by norm_num
example : wrongReturn 0 (ket 1 0) = 1 / 2 := by
  rw [pure_wrong_return_exact _ _ (ket_normalized _ _)]
  change 2 * transition 1 0 0 0 * (1 - transition 1 0 0 0) = _
  norm_num [transition_exact]
example : wrongReturn 0 (ket 0 0) = 0 := by
  rw [pure_wrong_return_exact _ _ (ket_normalized _ _)]
  change 2 * transition 0 0 0 0 * (1 - transition 0 0 0 0) = _
  norm_num [transition_exact]
example : wrongReturn 0 (ket 0 1) = 0 := by
  rw [pure_wrong_return_exact _ _ (ket_normalized _ _)]
  change 2 * transition 0 0 1 0 * (1 - transition 0 0 1 0) = _
  norm_num [transition_exact]
example : ∑ x : BB84Bit, (coinKraus x).conjTranspose * coinKraus x = 1 :=
  coin_kraus_complete
example (rho : QMatrix) : coinChannel rho = rho := coin_channel_identity rho
example : (coinKraus 0 * P 1 1 * (coinKraus 0).conjTranspose).trace = 1/2 := by
  apply coin_outcome_independent
  exact pure_trace (ket 1 1) (ket_normalized 1 1)
example : dephase 1 (P 1 0) = P 1 0 := known_basis_nondisturbance 1 0
example : PrometheusNQKDAuditSuite := verification_suite

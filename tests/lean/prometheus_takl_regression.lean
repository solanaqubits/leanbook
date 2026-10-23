import Verification.PrometheusTAKLAudit

open PrometheusTAKLAudit

example (phi : ℝ) : ‖unitPhase phi‖ = 1 := unit_phase_norm phi
example (phi : ℝ) : goldenRate 1 (unitPhase phi * (1 : ℂ)) 2 = goldenRate 1 1 2 :=
  global_phase_rate_invariant 1 2 phi 1
example : goldenRate 1 (0 : ℂ) 7 = 0 := by simp [goldenRate, goldenPrefactor]
example : 0 < goldenRate 1 (1 : ℂ) 2 :=
  rate_positive _ _ (by norm_num) (by norm_num) _ (by norm_num)
example : |goldenRate 1 (1 : ℂ) (2 + 1/100) - goldenRate 1 1 2| /
    goldenRate 1 1 2 ≤ 1/200 :=
  conditional_relative_rate_bound _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
example : |goldenRate 1 (1 : ℂ) (2 - 1/100) - goldenRate 1 1 2| /
    goldenRate 1 1 2 ≤ 1/200 := by
  simpa only [sub_eq_add_neg, neg_div] using conditional_relative_rate_bound 1 2 (-1/100) (1/200) 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
example : periodicDensity 1 (1/100) 0 = 1 := (density_three_values _ _).1
example : periodicDensity 1 (1/100) Real.pi = 51/50 := by
  rw [(density_three_values _ _).2.1]; norm_num
example : periodicDensity 1 (1/100) (2*Real.pi) = 1 := (density_three_values _ _).2.2
example : ¬ Monotone (periodicDensity 1 (1/100)) :=
  density_not_monotone _ _ (by norm_num) (by norm_num)
example (phi : ℝ) : 0 < periodicDensity 1 (1/100) phi :=
  periodic_density_positive _ _ (by norm_num) (by norm_num) phi
example : ¬ Monotone (fun phi => goldenRate 1 (1 : ℂ) (periodicDensity 1 (1/100) phi)) :=
  rate_not_monotone _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
example : Monotone (periodicDensity 1 0) := by intro x y _; simp [periodicDensity]
example (phi : ℝ) : periodicDensity 2 (1/100) (phi + 2*Real.pi) =
    periodicDensity 2 (1/100) phi := density_periodic _ _ phi
example (R E mu h c : ℝ) : acPhase R (-E) mu h c = -acPhase R E mu h c :=
  orientation_reversal R E mu h c
example (R mu h c : ℝ) : acPhase R 0 mu h c = 0 := by simp [acPhase]
example : canonicalMomentum 2 3 4 = 11 := by norm_num [canonicalMomentum]
example : ringHamiltonian 2 3 11 = 16 := by norm_num [ringHamiltonian]
example : canonicalMomentum 2 3 4 * 4 - ringLagrangian 2 3 4 =
    ringHamiltonian 2 3 (canonicalMomentum 2 3 4) :=
  legendre_identity 2 3 4 (by norm_num)
example (phi : ℝ) (ell : ℤ) : ringEnergy 1 1 1 (phi + 2*Real.pi) (ell+1) =
    ringEnergy 1 1 1 phi ell := flux_relabel _ _ _ _ _
example : ringEnergy 1 1 1 0 0 = 0 := by norm_num [ringEnergy]
example : ringEnergy 1 1 1 0 1 = 1/2 := by norm_num [ringEnergy]
example (phi : ℝ) (ell : ℤ) : 0 ≤ ringEnergy 1 1 1 phi ell :=
  ring_energy_nonnegative _ _ _ _ _ (by norm_num)
example : PrometheusTAKLAuditSuite := verification_suite

-- Explicit model-specific field bound; no measured beta-density dependence is assumed.
example (E : ℝ) :
    |goldenRate 1 (1 : ℂ) (periodicDensity 2 (1/100) (acPhase 1 E 1 1 1)) -
        goldenRate 1 1 2| / goldenRate 1 1 2 ≤ (1/100) * (acPhase 1 E 1 1 1)^2 / 2 :=
  periodic_ac_relative_bound 1 2 (1/100) 1 E 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

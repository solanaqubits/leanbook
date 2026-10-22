import Verification.PrometheusUCNAudit

open PrometheusUCNAudit

example : reactionRate 3 5 2 = 15 := by norm_num [reactionRate, crossSection]
example : reactionRate 3 5 (1 / 100) = 15 := by norm_num [reactionRate, crossSection]
example : reactionRate 3 5 0 ≠ 15 := by norm_num [reactionRate, crossSection]
example : holdingProbability 3 5 2 7 = holdingProbability 3 5 (1 / 100) 7 :=
  fixed_time_invariant _ _ _ _ _ (by norm_num) (by norm_num)
example : slabProbability 3 5 7 2 < slabProbability 3 5 7 1 :=
  slab_strict_decrease _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
example : ¬slabProbability 0 5 7 2 < slabProbability 0 5 7 1 := by simp [slabProbability]
example : asymmetry 12 0 = 1 := neutron_asymmetry 12 (by norm_num)
example : asymmetry 0 0 ≠ 1 := by norm_num [asymmetry]
example : asymmetry 0 12 = -1 := by norm_num [asymmetry]
example : asymmetry 12 12 = 0 := symmetric_asymmetry 12
example : eosAtSaturation 30 (asymmetry 12 0) = 14 := by norm_num [eosAtSaturation, asymmetry]
example : eosAtSaturation 0 (asymmetry 12 0) < 0 := by norm_num [eosAtSaturation, asymmetry]
example : eosAtSaturation 30 0 = -16 := symmetric_energy 30
example : 0 < eosAtSaturation 30 (asymmetry 12 0) :=
  (neutron_energy_lower_bound _ _ (by norm_num) (by norm_num)).2
-- Dimensionless numeric mass inputs are algebra witnesses, not physical masses.
example : qValue 12 100 1008 1 = 192 := by norm_num [qValue]
example : qValue 12 100 1200 1 = 0 := by norm_num [qValue]
example : qValue 12 100 1300 1 < 0 := by norm_num [qValue]
example : qValue 12 100 1008 1 = 192 ↔ (1008 : ℝ) * 1 ^ 2 = 12 * 100 * 1 ^ 2 - 192 :=
  q192_iff_mass _ _ _
example : joulePerMeV = 1602176634 / 10000000000000000000000 := rfl
example : hypotheticalGross = 25634826144 / 1000000000000000000 := by
  norm_num [hypotheticalGross, joulePerMeV]
example : hypotheticalGross < 26 / 1000000000 := gross_bounds.2
example : hypotheticalGross - 1 < 0 := net_deficit 1 (by norm_num)
example : 0 < hypotheticalGross - 0 := by simpa using gross_bounds.1

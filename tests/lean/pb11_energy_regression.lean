import Verification.PB11EnergyBalance

open PB11EnergyBalance

noncomputable section

/-- Algebraic satisfiability witness only; these are not measured rest energies. -/
def toyReaction : PB11Reaction where
  m_p := 1
  m_B := 107 / 10
  m_alpha := 1
  Q := 87 / 10
  m_p_nonneg := by norm_num
  m_B_nonneg := by norm_num
  m_alpha_nonneg := by norm_num
  q_eq := rfl
  mass_defect := by norm_num

def collector : MHDExtractor where
  B := 2
  v := 1
  eta := 3 / 5
  B_nonneg := by norm_num
  v_nonneg := by norm_num
  eta_nonneg := by norm_num
  eta_le_one := by norm_num

example : toyReaction.kineticOut (27 / 40) = 75 / 8 := by
  norm_num [PB11Reaction.kineticOut, toyReaction]

example (r : PB11Reaction) (k : ℝ) :
    r.m_p + r.m_B + k = 3 * r.m_alpha + r.kineticOut k := energy_conservation r k

example (r : PB11Reaction) (k : ℝ) (hk : 0 ≤ k) : 0 ≤ r.kineticOut k :=
  kineticOut_nonneg r k hk

example : collector.workOut 10 = 6 := by norm_num [MHDExtractor.workOut, collector]
example : collector.workOut 10 ≤ 10 := mhd_bound collector 10 (by norm_num)

-- Removing the kinetic-energy sign premise makes the requested bound false.
example : ¬ (3 / 5 : ℝ) * (-10) ≤ -10 := by norm_num
-- Independent masses do not imply the proposed 8.7 MeV mass defect.
example : (1 : ℝ) + 1 + 0 ≠ 3 * 1 + (0 + 87 / 10) := by norm_num

example : fusionEnergy baseline = 29 / 150000 := by
  norm_num [fusionEnergy, baseline]
example : alphaEnergy baseline = 1 / 4800 := by
  norm_num [alphaEnergy, fusionEnergy, baseline]
example : electricalEnergy baseline = 1 / 8000 := baseline_output
example : electricalEnergy baseline / baseline.laser = 1 / 12000 := by
  rw [baseline_output]
  norm_num [baseline]
example : fusionEnergy baseline / baseline.laser = 29 / 225000 := by
  norm_num [fusionEnergy, baseline]
example : grossPower baseline 1000 = 1 / 8 := baseline_gross_1000
example : grossPower baseline 8000000 = 1000 := baseline_frequency
example : netPower baseline 8000000 1 0 0 = -11999000 := by
  unfold netPower
  rw [baseline_output]
  norm_num [baseline]

example (f w a p : ℝ) (hf : 0 ≤ f) (hw : 0 < w) (hw1 : w ≤ 1)
    (ha : 0 ≤ a) (hp : 0 ≤ p) : netPower baseline f w a p < 1000 := by
  have h := baseline_net_nonpositive f w a p hf hw hw1 ha hp
  linarith

example (s : Shot) : s.laser + fusionEnergy s =
    electricalEnergy s + laserLoss s + protonLoss s + alphaLoss s := shot_balance s
example (s : Shot) : 0 ≤ laserLoss s ∧ 0 ≤ protonLoss s ∧ 0 ≤ alphaLoss s :=
  losses_nonneg s
example (s : Shot) : fusionEnergy s = reactionCount s * s.qMeV * mevToJ :=
  fusion_from_count s
example (s : Shot) : electricalEnergy s ≤ s.laser + fusionEnergy s :=
  electrical_le_available s

def noReaction : Shot :=
  { baseline with
    probability := 0
    probability_nonneg := by norm_num
    probability_le_one := by norm_num }

def noExtraction : Shot :=
  { baseline with
    eta := 0
    eta_nonneg := by norm_num
    eta_le_one := by norm_num }

example : electricalEnergy noReaction = 0 := by
  unfold noReaction
  norm_num [electricalEnergy, alphaEnergy, fusionEnergy]
example : electricalEnergy noExtraction = 0 := by
  simp [electricalEnergy, noExtraction]

end

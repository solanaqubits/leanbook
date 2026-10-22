/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Conditional scalar p–B11 energy bookkeeping

Rest energies are in MeV (m c²), not masses in kilograms. The mass defect is
an explicit premise. Q = 8.7 is exact in this model, not an exact measured value.
Extraction efficiency is energetic, not merely charge collection efficiency.
No plasma dynamics, electrode topology, fuel availability, physical calibration
or authority/hardware qualification is established by this module.
-/

namespace PB11EnergyBalance

noncomputable section

structure PB11Reaction where
  m_p : ℝ
  m_B : ℝ
  m_alpha : ℝ
  Q : ℝ
  m_p_nonneg : 0 ≤ m_p
  m_B_nonneg : 0 ≤ m_B
  m_alpha_nonneg : 0 ≤ m_alpha
  q_eq : Q = 87 / 10
  mass_defect : m_p + m_B = 3 * m_alpha + Q

/-- Sum of product kinetic energies for a stationary target in this model. -/
def PB11Reaction.kineticOut (r : PB11Reaction) (kineticIn : ℝ) : ℝ :=
  kineticIn + r.Q

theorem energy_conservation (r : PB11Reaction) (kineticIn : ℝ) :
    r.m_p + r.m_B + kineticIn = 3 * r.m_alpha + r.kineticOut kineticIn := by
  dsimp [PB11Reaction.kineticOut]
  linarith [r.mass_defect]

theorem kineticOut_nonneg (r : PB11Reaction) (kineticIn : ℝ) (h : 0 ≤ kineticIn) :
    0 ≤ r.kineticOut kineticIn := by
  dsimp [PB11Reaction.kineticOut]
  rw [r.q_eq]
  linarith

/-- B and v are nonnegative magnitudes; their dynamics are not modeled. -/
structure MHDExtractor where
  B : ℝ
  v : ℝ
  eta : ℝ
  B_nonneg : 0 ≤ B
  v_nonneg : 0 ≤ v
  eta_nonneg : 0 ≤ eta
  eta_le_one : eta ≤ 1

def MHDExtractor.workOut (e : MHDExtractor) (kineticOut : ℝ) : ℝ :=
  e.eta * kineticOut

theorem workOut_nonneg (e : MHDExtractor) (kineticOut : ℝ) (h : 0 ≤ kineticOut) :
    0 ≤ e.workOut kineticOut := mul_nonneg e.eta_nonneg h

theorem mhd_bound (e : MHDExtractor) (kineticOut : ℝ) (h : 0 ≤ kineticOut) :
    e.workOut kineticOut ≤ kineticOut := by
  exact mul_le_of_le_one_left h e.eta_le_one

/-- Optical energy in joules; proton and reaction energies both in MeV. -/
structure Shot where
  laser : ℝ
  acceleration : ℝ
  probability : ℝ
  eta : ℝ
  protonMeV : ℝ
  qMeV : ℝ
  laser_nonneg : 0 ≤ laser
  acceleration_nonneg : 0 ≤ acceleration
  acceleration_le_one : acceleration ≤ 1
  probability_nonneg : 0 ≤ probability
  probability_le_one : probability ≤ 1
  eta_nonneg : 0 ≤ eta
  eta_le_one : eta ≤ 1
  proton_pos : 0 < protonMeV
  q_eq : qMeV = 87 / 10

/-- Exact SI conversion, in joules per MeV. -/
def mevToJ : ℝ := 1602176634 / 10000000000000000000000

def protonCount (s : Shot) : ℝ := s.acceleration * s.laser / (s.protonMeV * mevToJ)
def reactionCount (s : Shot) : ℝ := s.probability * protonCount s
def fusionEnergy (s : Shot) : ℝ :=
  s.probability * (s.acceleration * s.laser) * (s.qMeV / s.protonMeV)
def alphaEnergy (s : Shot) : ℝ :=
  s.probability * (s.acceleration * s.laser) + fusionEnergy s
def electricalEnergy (s : Shot) : ℝ := s.eta * alphaEnergy s
def laserLoss (s : Shot) : ℝ := (1 - s.acceleration) * s.laser
def protonLoss (s : Shot) : ℝ := (1 - s.probability) * (s.acceleration * s.laser)
def alphaLoss (s : Shot) : ℝ := (1 - s.eta) * alphaEnergy s

/-- Counts are expected real amounts; the unit conversion cancels exactly. -/
theorem fusion_from_count (s : Shot) :
    fusionEnergy s = reactionCount s * s.qMeV * mevToJ := by
  unfold fusionEnergy reactionCount protonCount
  have hc : mevToJ ≠ 0 := by norm_num [mevToJ]
  field_simp

theorem fusion_nonneg (s : Shot) : 0 ≤ fusionEnergy s := by
  apply mul_nonneg (mul_nonneg s.probability_nonneg
    (mul_nonneg s.acceleration_nonneg s.laser_nonneg))
  rw [s.q_eq]
  exact div_nonneg (by norm_num) s.proton_pos.le

theorem alpha_nonneg (s : Shot) : 0 ≤ alphaEnergy s :=
  add_nonneg (mul_nonneg s.probability_nonneg
    (mul_nonneg s.acceleration_nonneg s.laser_nonneg)) (fusion_nonneg s)

theorem electrical_bounds (s : Shot) :
    0 ≤ electricalEnergy s ∧ electricalEnergy s ≤ alphaEnergy s :=
  ⟨mul_nonneg s.eta_nonneg (alpha_nonneg s),
    mul_le_of_le_one_left (alpha_nonneg s) s.eta_le_one⟩

theorem losses_nonneg (s : Shot) :
    0 ≤ laserLoss s ∧ 0 ≤ protonLoss s ∧ 0 ≤ alphaLoss s :=
  ⟨mul_nonneg (sub_nonneg.mpr s.acceleration_le_one) s.laser_nonneg,
    mul_nonneg (sub_nonneg.mpr s.probability_le_one)
      (mul_nonneg s.acceleration_nonneg s.laser_nonneg),
    mul_nonneg (sub_nonneg.mpr s.eta_le_one) (alpha_nonneg s)⟩

/-- Released nuclear rest energy is included on the input side. -/
theorem shot_balance (s : Shot) :
    s.laser + fusionEnergy s =
      electricalEnergy s + laserLoss s + protonLoss s + alphaLoss s := by
  unfold electricalEnergy laserLoss protonLoss alphaLoss alphaEnergy
  ring

theorem electrical_le_available (s : Shot) :
    electricalEnergy s ≤ s.laser + fusionEnergy s := by
  have h := losses_nonneg s
  linarith [shot_balance s]

def grossPower (s : Shot) (frequency : ℝ) : ℝ := frequency * electricalEnergy s
def netPower (s : Shot) (frequency wallEfficiency auxShot auxPower : ℝ) : ℝ :=
  frequency * (electricalEnergy s - s.laser / wallEfficiency - auxShot) - auxPower

/-- A no-gain optical scenario cannot acquire net gain through imperfect supply. -/
theorem net_nonpositive_of_no_gain (s : Shot) (frequency wallEfficiency auxShot auxPower : ℝ)
    (hf : 0 ≤ frequency) (hw : 0 < wallEfficiency) (hw1 : wallEfficiency ≤ 1)
    (ha : 0 ≤ auxShot) (hp : 0 ≤ auxPower) (hg : electricalEnergy s ≤ s.laser) :
    netPower s frequency wallEfficiency auxShot auxPower ≤ 0 := by
  have hinput : s.laser ≤ s.laser / wallEfficiency := by
    apply (le_div_iff₀ hw).2
    exact mul_le_of_le_one_right s.laser_nonneg hw1
  have hd : electricalEnergy s - s.laser / wallEfficiency - auxShot ≤ 0 := by linarith
  have hm := mul_nonpos_of_nonneg_of_nonpos hf hd
  unfold netPower
  linarith

/-- User-selected exact scenario; not a measured reactor calibration. -/
def baseline : Shot where
  laser := 3 / 2
  acceleration := 1 / 10
  probability := 1 / 10000
  eta := 3 / 5
  protonMeV := 27 / 40
  qMeV := 87 / 10
  laser_nonneg := by norm_num
  acceleration_nonneg := by norm_num
  acceleration_le_one := by norm_num
  probability_nonneg := by norm_num
  probability_le_one := by norm_num
  eta_nonneg := by norm_num
  eta_le_one := by norm_num
  proton_pos := by norm_num
  q_eq := rfl

theorem baseline_output : electricalEnergy baseline = 1 / 8000 := by
  norm_num [electricalEnergy, alphaEnergy, fusionEnergy, baseline]

theorem baseline_gross_1000 : grossPower baseline 1000 = 1 / 8 := by
  norm_num [grossPower, baseline_output]

theorem baseline_frequency : grossPower baseline 8000000 = 1000 := by
  norm_num [grossPower, baseline_output]

theorem baseline_net_nonpositive (frequency wallEfficiency auxShot auxPower : ℝ)
    (hf : 0 ≤ frequency) (hw : 0 < wallEfficiency) (hw1 : wallEfficiency ≤ 1)
    (ha : 0 ≤ auxShot) (hp : 0 ≤ auxPower) :
    netPower baseline frequency wallEfficiency auxShot auxPower ≤ 0 := by
  apply net_nonpositive_of_no_gain baseline frequency wallEfficiency auxShot auxPower
    hf hw hw1 ha hp
  rw [baseline_output]
  norm_num [baseline]

structure PB11EnergyBalanceSuite : Prop where
  reaction : ∀ r k, r.m_p + r.m_B + k = 3 * r.m_alpha + PB11Reaction.kineticOut r k
  extraction : ∀ e k, 0 ≤ k → MHDExtractor.workOut e k ≤ k
  balance : ∀ s, s.laser + fusionEnergy s =
    electricalEnergy s + laserLoss s + protonLoss s + alphaLoss s
  losses : ∀ s, 0 ≤ laserLoss s ∧ 0 ≤ protonLoss s ∧ 0 ≤ alphaLoss s
  output : electricalEnergy baseline = 1 / 8000
  no_autonomy : ∀ f w a p, 0 ≤ f → 0 < w → w ≤ 1 → 0 ≤ a → 0 ≤ p →
    netPower baseline f w a p ≤ 0

theorem verification_suite : PB11EnergyBalanceSuite :=
  ⟨energy_conservation, mhd_bound, shot_balance, losses_nonneg, baseline_output,
    baseline_net_nonpositive⟩

end
end PB11EnergyBalance

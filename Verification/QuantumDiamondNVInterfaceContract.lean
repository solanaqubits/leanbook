/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ideal NV population and coherent pi-pulse contracts

Rational normalized populations and a stipulated optical pumping map are separate
from complex amplitudes. `Represents` is a conditional bridge, not a rounding map.
No physical calibration, intersystem-crossing mechanism, Rabi-time relation or
spin-coherence preservation by optical pumping is asserted.
-/
namespace QuantumDiamondNVInterfaceContract

inductive NVSpinState where
  | Zero | Plus | Minus
  deriving DecidableEq, Repr

@[ext] structure NVSpinPopulation where
  p0 : ℚ
  pPlus : ℚ
  pMinus : ℚ
  h_p0_nonneg : 0 ≤ p0
  h_pPlus_nonneg : 0 ≤ pPlus
  h_pMinus_nonneg : 0 ≤ pMinus
  h_sum_one : p0 + pPlus + pMinus = 1

def purePopulation : NVSpinState → NVSpinPopulation
  | .Zero => ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | .Plus => ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | .Minus => ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

def residual (p : NVSpinPopulation) : ℚ := p.pPlus + p.pMinus

theorem population_bounds (p : NVSpinPopulation) :
    0 ≤ p.p0 ∧ p.p0 ≤ 1 ∧ 0 ≤ p.pPlus ∧ p.pPlus ≤ 1 ∧
      0 ≤ p.pMinus ∧ p.pMinus ≤ 1 := by
  have h0 := p.h_p0_nonneg
  have hp := p.h_pPlus_nonneg
  have hm := p.h_pMinus_nonneg
  have hs := p.h_sum_one
  exact ⟨h0, by linarith, hp, by linarith, hm, by linarith⟩

/-- The explicit proof argument excludes efficiencies outside [0,1]. -/
def opticalPumpStep (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation) : NVSpinPopulation where
  p0 := p.p0 + η * (p.pPlus + p.pMinus)
  pPlus := (1 - η) * p.pPlus
  pMinus := (1 - η) * p.pMinus
  h_p0_nonneg := add_nonneg p.h_p0_nonneg
    (mul_nonneg hη.1 (add_nonneg p.h_pPlus_nonneg p.h_pMinus_nonneg))
  h_pPlus_nonneg := mul_nonneg (sub_nonneg.mpr hη.2) p.h_pPlus_nonneg
  h_pMinus_nonneg := mul_nonneg (sub_nonneg.mpr hη.2) p.h_pMinus_nonneg
  h_sum_one := by
    calc
      _ = p.p0 + p.pPlus + p.pMinus := by ring
      _ = 1 := p.h_sum_one

def pumpCycles (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) : ℕ → NVSpinPopulation → NVSpinPopulation
  | 0, p => p
  | k + 1, p => opticalPumpStep η hη (pumpCycles η hη k p)

theorem optical_pump_population_bounds (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation) :
    0 ≤ (opticalPumpStep η hη p).p0 ∧ (opticalPumpStep η hη p).p0 ≤ 1 ∧
    0 ≤ (opticalPumpStep η hη p).pPlus ∧ (opticalPumpStep η hη p).pPlus ≤ 1 ∧
    0 ≤ (opticalPumpStep η hη p).pMinus ∧ (opticalPumpStep η hη p).pMinus ≤ 1 :=
  population_bounds _

theorem optical_pump_p0_monotonicity (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation) :
    p.p0 ≤ (opticalPumpStep η hη p).p0 := by
  exact le_add_of_nonneg_right (mul_nonneg hη.1 (add_nonneg p.h_pPlus_nonneg p.h_pMinus_nonneg))

theorem optical_pump_residual (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation) :
    residual (opticalPumpStep η hη p) = (1 - η) * residual p := by
  dsimp [residual, opticalPumpStep]
  ring

/-- Exact finite-cycle residual, not an assertion of finite exact polarization. -/
theorem optical_pump_convergence (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1)
    (k : ℕ) (p : NVSpinPopulation) :
    residual (pumpCycles η hη k p) = (1 - η) ^ k * residual p := by
  induction k with
  | zero => simp [pumpCycles]
  | succ k ih => rw [pumpCycles, optical_pump_residual, ih, pow_succ]; ring

theorem optical_pump_p0_exact (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1)
    (k : ℕ) (p : NVSpinPopulation) :
    (pumpCycles η hη k p).p0 = 1 - (1 - η) ^ k * residual p := by
  have hs := (pumpCycles η hη k p).h_sum_one
  have hr := optical_pump_convergence η hη k p
  dsimp [residual] at hr ⊢
  linarith

theorem optical_pump_zero (hη : (0 : ℚ) ≤ 0 ∧ 0 ≤ 1) (p : NVSpinPopulation) :
    opticalPumpStep 0 hη p = p := by ext <;> simp [opticalPumpStep]

theorem pump_cycles_zero_efficiency (hη : (0 : ℚ) ≤ 0 ∧ 0 ≤ 1)
    (k : ℕ) (p : NVSpinPopulation) : pumpCycles 0 hη k p = p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pumpCycles, optical_pump_zero, ih]

theorem optical_pump_one (hη : (0 : ℚ) ≤ 1 ∧ 1 ≤ 1) (p : NVSpinPopulation) :
    opticalPumpStep 1 hη p = purePopulation .Zero := by
  ext <;> simp [opticalPumpStep, purePopulation]
  linarith [p.h_sum_one]

theorem finite_residual_positive (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (hηlt : η < 1)
    (k : ℕ) (p : NVSpinPopulation) (hp : 0 < residual p) :
    0 < residual (pumpCycles η hη k p) := by
  rw [optical_pump_convergence]
  exact mul_pos (pow_pos (sub_pos.mpr hηlt) _) hp

theorem finite_p0_lt_one (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (hηlt : η < 1)
    (k : ℕ) (p : NVSpinPopulation) (hp : 0 < residual p) :
    (pumpCycles η hη k p).p0 < 1 := by
  have hr := finite_residual_positive η hη hηlt k p hp
  have hs := (pumpCycles η hη k p).h_sum_one
  dsimp [residual] at hr
  linarith

theorem optical_pump_asymptotic_limit (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (hpos : 0 < η)
    (p : NVSpinPopulation) :
    Filter.Tendsto (fun k : ℕ => ((pumpCycles η hη k p).p0 : ℝ)) Filter.atTop (nhds 1) := by
  have hb0 : (0 : ℝ) ≤ 1 - (η : ℝ) := by exact_mod_cast (sub_nonneg.mpr hη.2)
  have hb1 : 1 - (η : ℝ) < 1 := by
    have he : (0 : ℝ) < η := by exact_mod_cast hpos
    linarith
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1).mul_const (residual p : ℝ)
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  have ht := hconst.sub hp
  simp only [zero_mul, sub_zero] at ht
  convert ht using 1
  ext k
  rw [optical_pump_p0_exact]
  push_cast
  rfl

def luminescenceYield (r0 r_dark : ℚ) (p : NVSpinPopulation) : ℚ :=
  r0 * p.p0 + r_dark * (p.pPlus + p.pMinus)

theorem luminescence_affine (r0 r_dark : ℚ) (p : NVSpinPopulation) :
    luminescenceYield r0 r_dark p = r_dark + (r0 - r_dark) * p.p0 := by
  calc
    _ = r_dark * (p.p0 + p.pPlus + p.pMinus) + (r0 - r_dark) * p.p0 := by
      dsimp [luminescenceYield]
      ring
    _ = _ := by rw [p.h_sum_one]; ring

theorem luminescence_difference (r0 r_dark : ℚ) (p q : NVSpinPopulation) :
    luminescenceYield r0 r_dark q - luminescenceYield r0 r_dark p =
      (r0 - r_dark) * (q.p0 - p.p0) := by
  rw [luminescence_affine, luminescence_affine]
  ring

theorem readout_contrast_monotonicity (r0 r_dark : ℚ) (hr : r_dark ≤ r0)
    (p q : NVSpinPopulation) (hp : p.p0 ≤ q.p0) :
    luminescenceYield r0 r_dark p ≤ luminescenceYield r0 r_dark q := by
  have h := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hp)
  rw [← luminescence_difference] at h
  exact sub_nonneg.mp h

theorem readout_contrast_strict_mono (r0 r_dark : ℚ) (hr : r_dark < r0)
    (p q : NVSpinPopulation) :
    luminescenceYield r0 r_dark p < luminescenceYield r0 r_dark q ↔ p.p0 < q.p0 := by
  constructor
  · intro h
    have hd := luminescence_difference r0 r_dark p q
    nlinarith
  · intro h
    have hm := mul_pos (sub_pos.mpr hr) (sub_pos.mpr h)
    rw [← luminescence_difference] at hm
    exact sub_pos.mp hm

theorem luminescence_between (r0 r_dark : ℚ) (hr : r_dark ≤ r0) (p : NVSpinPopulation) :
    r_dark ≤ luminescenceYield r0 r_dark p ∧ luminescenceYield r0 r_dark p ≤ r0 := by
  rw [luminescence_affine]
  have hb := population_bounds p
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hr) p.h_p0_nonneg,
    mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hb.2.1)]

theorem luminescence_nonneg (r0 r_dark : ℚ) (hd : 0 ≤ r_dark) (hr : r_dark ≤ r0)
    (p : NVSpinPopulation) : 0 ≤ luminescenceYield r0 r_dark p :=
  hd.trans (luminescence_between r0 r_dark hr p).1

theorem luminescence_contrast_bound (r0 r_dark : ℚ) (hr : r_dark < r0)
    (p : NVSpinPopulation) (hp : 0 < residual p) :
    luminescenceYield r0 r_dark p < luminescenceYield r0 r_dark (purePopulation .Zero) := by
  apply (readout_contrast_strict_mono r0 r_dark hr p _).mpr
  change p.p0 < 1
  dsimp [residual] at hp
  linarith [p.h_sum_one]

def mwPiPulseStep (p : NVSpinPopulation) : NVSpinPopulation where
  p0 := p.pMinus
  pPlus := p.pPlus
  pMinus := p.p0
  h_p0_nonneg := p.h_pMinus_nonneg
  h_pPlus_nonneg := p.h_pPlus_nonneg
  h_pMinus_nonneg := p.h_p0_nonneg
  h_sum_one := by linarith [p.h_sum_one]

theorem mw_pi_pulse_involution (p : NVSpinPopulation) :
    mwPiPulseStep (mwPiPulseStep p) = p := by ext <;> rfl

abbrev CoherentAmp := ℂ × ℂ × ℂ

/-- Coordinates are ordered Zero, Plus, Minus. -/
def coherentPi (a : CoherentAmp) : CoherentAmp :=
  (-Complex.I * a.2.2, a.2.1, -Complex.I * a.1)

def coherentPiInverse (a : CoherentAmp) : CoherentAmp :=
  (Complex.I * a.2.2, a.2.1, Complex.I * a.1)

def ampIntensity (a : CoherentAmp) : ℝ :=
  Complex.normSq a.1 + Complex.normSq a.2.1 + Complex.normSq a.2.2

theorem coherent_pi_add (a b : CoherentAmp) : coherentPi (a + b) = coherentPi a + coherentPi b := by
  apply Prod.ext
  · simp [coherentPi, mul_add]
  · apply Prod.ext <;> simp [coherentPi, mul_add]

theorem coherent_pi_smul (c : ℂ) (a : CoherentAmp) : coherentPi (c • a) = c • coherentPi a := by
  apply Prod.ext
  · simp [coherentPi, mul_left_comm]
  · apply Prod.ext <;> simp [coherentPi, mul_left_comm]

theorem coherent_pi_intensity (a : CoherentAmp) : ampIntensity (coherentPi a) = ampIntensity a := by
  simp [ampIntensity, coherentPi, Complex.normSq_mul]
  ring

theorem coherent_pi_inverse_left (a : CoherentAmp) : coherentPiInverse (coherentPi a) = a := by
  apply Prod.ext
  · simp [coherentPiInverse, coherentPi, ← mul_assoc]
  · apply Prod.ext <;> simp [coherentPiInverse, coherentPi, ← mul_assoc]

theorem coherent_pi_inverse_right (a : CoherentAmp) : coherentPi (coherentPiInverse a) = a := by
  apply Prod.ext
  · simp [coherentPiInverse, coherentPi, ← mul_assoc]
  · apply Prod.ext <;> simp [coherentPiInverse, coherentPi, ← mul_assoc]

/-- Two pi pulses retain a relative phase against the unaffected Plus component. -/
theorem coherent_pi_twice (a : CoherentAmp) :
    coherentPi (coherentPi a) = (-a.1, a.2.1, -a.2.2) := by
  apply Prod.ext
  · simp [coherentPi, ← mul_assoc]
  · apply Prod.ext <;> simp [coherentPi, ← mul_assoc]

theorem coherent_pi_difference_intensity (a b : CoherentAmp) :
    ampIntensity (coherentPi a - coherentPi b) = ampIntensity (a - b) := by
  have hn : coherentPi (-b) = -coherentPi b := by simpa using coherent_pi_smul (-1) b
  rw [sub_eq_add_neg, ← hn, ← coherent_pi_add, ← sub_eq_add_neg, coherent_pi_intensity]

/-- Only amplitudes with these exact rational squared norms represent this population. -/
def Represents (a : CoherentAmp) (p : NVSpinPopulation) : Prop :=
  Complex.normSq a.1 = (p.p0 : ℝ) ∧ Complex.normSq a.2.1 = (p.pPlus : ℝ) ∧
    Complex.normSq a.2.2 = (p.pMinus : ℝ)

theorem represents_normalized (a : CoherentAmp) (p : NVSpinPopulation) (h : Represents a p) :
    ampIntensity a = 1 := by
  dsimp [ampIntensity]
  rw [h.1, h.2.1, h.2.2]
  exact_mod_cast p.h_sum_one

theorem coherent_pi_population_bridge (a : CoherentAmp) (p : NVSpinPopulation)
    (h : Represents a p) : Represents (coherentPi a) (mwPiPulseStep p) := by
  simpa [Represents, coherentPi, mwPiPulseStep, Complex.normSq_mul] using
    And.intro h.2.2 (And.intro h.2.1 h.1)

structure QuantumDiamondNVInterfaceSuite : Prop where
  pumping_bounds : ∀ (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation),
    0 ≤ (opticalPumpStep η hη p).p0 ∧ (opticalPumpStep η hη p).p0 ≤ 1 ∧
    0 ≤ (opticalPumpStep η hη p).pPlus ∧ (opticalPumpStep η hη p).pPlus ≤ 1 ∧
    0 ≤ (opticalPumpStep η hη p).pMinus ∧ (opticalPumpStep η hη p).pMinus ≤ 1
  pumping_monotonicity : ∀ (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation),
    p.p0 ≤ (opticalPumpStep η hη p).p0
  finite_residual : ∀ (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (k : ℕ) (p : NVSpinPopulation),
    residual (pumpCycles η hη k p) = (1 - η) ^ k * residual p
  pumping_limit : ∀ (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1), 0 < η → ∀ p : NVSpinPopulation,
    Filter.Tendsto (fun k : ℕ => ((pumpCycles η hη k p).p0 : ℝ)) Filter.atTop (nhds 1)
  population_involution : ∀ p : NVSpinPopulation, mwPiPulseStep (mwPiPulseStep p) = p
  readout_monotonicity : ∀ (r0 r_dark : ℚ), r_dark ≤ r0 → ∀ p q : NVSpinPopulation,
    p.p0 ≤ q.p0 → luminescenceYield r0 r_dark p ≤ luminescenceYield r0 r_dark q
  strict_readout : ∀ (r0 r_dark : ℚ), r_dark < r0 → ∀ p q : NVSpinPopulation,
    luminescenceYield r0 r_dark p < luminescenceYield r0 r_dark q ↔ p.p0 < q.p0
  bright_contrast : ∀ (r0 r_dark : ℚ), r_dark < r0 → ∀ p : NVSpinPopulation,
    0 < residual p →
      luminescenceYield r0 r_dark p < luminescenceYield r0 r_dark (purePopulation .Zero)
  coherent_add : ∀ a b : CoherentAmp, coherentPi (a + b) = coherentPi a + coherentPi b
  coherent_smul : ∀ (c : ℂ) (a : CoherentAmp), coherentPi (c • a) = c • coherentPi a
  coherent_intensity : ∀ a : CoherentAmp, ampIntensity (coherentPi a) = ampIntensity a
  coherent_inverse : ∀ a : CoherentAmp, coherentPiInverse (coherentPi a) = a
  coherent_inverse_right : ∀ a : CoherentAmp, coherentPi (coherentPiInverse a) = a
  coherent_double_phase : ∀ a : CoherentAmp, coherentPi (coherentPi a) = (-a.1, a.2.1, -a.2.2)
  population_bridge : ∀ (a : CoherentAmp) (p : NVSpinPopulation),
    Represents a p → Represents (coherentPi a) (mwPiPulseStep p)

theorem verification_suite : QuantumDiamondNVInterfaceSuite := {
  pumping_bounds := optical_pump_population_bounds
  pumping_monotonicity := optical_pump_p0_monotonicity
  finite_residual := optical_pump_convergence
  pumping_limit := optical_pump_asymptotic_limit
  population_involution := mw_pi_pulse_involution
  readout_monotonicity := readout_contrast_monotonicity
  strict_readout := readout_contrast_strict_mono
  bright_contrast := luminescence_contrast_bound
  coherent_add := coherent_pi_add
  coherent_smul := coherent_pi_smul
  coherent_intensity := coherent_pi_intensity
  coherent_inverse := coherent_pi_inverse_left
  coherent_inverse_right := coherent_pi_inverse_right
  coherent_double_phase := coherent_pi_twice
  population_bridge := coherent_pi_population_bridge
}

end QuantumDiamondNVInterfaceContract

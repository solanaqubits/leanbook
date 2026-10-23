/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Conditional Aharonov--Casher ring and decay-density audit

This is a nonrelativistic scalar ring model plus conditional golden-rule algebra.
It is not a weak-interaction QFT derivation. Center-of-mass ring energies/density
are not identified with the final-state density entering neutron beta decay.
A global amplitude phase alone does not change the decay rate. Any density change
is an additional hypothesis, and a positive periodic density need not be monotone.
-/
namespace PrometheusTAKLAudit
noncomputable section

/-- The supplied density is the relevant final-state density, not automatically ring COM DOS. -/
def goldenPrefactor (hbar : ℝ) (amplitude : ℂ) : ℝ :=
  (2 * Real.pi / hbar) * ‖amplitude‖ ^ 2

def goldenRate (hbar : ℝ) (amplitude : ℂ) (density : ℝ) : ℝ :=
  goldenPrefactor hbar amplitude * density

def unitPhase (phi : ℝ) : ℂ := Complex.exp ((phi : ℂ) * Complex.I)

theorem unit_phase_norm (phi : ℝ) : ‖unitPhase phi‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I phi

theorem phase_amplitude_norm (phi : ℝ) (amplitude : ℂ) :
    ‖unitPhase phi * amplitude‖ = ‖amplitude‖ := by
  rw [Complex.norm_mul, unit_phase_norm, one_mul]

theorem global_phase_rate_invariant (hbar density phi : ℝ) (amplitude : ℂ) :
    goldenRate hbar (unitPhase phi * amplitude) density = goldenRate hbar amplitude density := by
  simp only [goldenRate, goldenPrefactor, phase_amplitude_norm]

theorem prefactor_positive (hbar : ℝ) (hh : 0 < hbar) (amplitude : ℂ)
    (ha : amplitude ≠ 0) : 0 < goldenPrefactor hbar amplitude := by
  have hn : 0 < ‖amplitude‖ := norm_pos_iff.mpr ha
  unfold goldenPrefactor
  positivity

theorem rate_positive (hbar density : ℝ) (hh : 0 < hbar) (hrho : 0 < density)
    (amplitude : ℂ) (ha : amplitude ≠ 0) : 0 < goldenRate hbar amplitude density :=
  mul_pos (prefactor_positive hbar hh amplitude ha) hrho

/-- Fixed amplitude and positive baseline are essential to this relative bound. -/
theorem conditional_relative_rate_bound (hbar rho0 delta epsilon : ℝ)
    (amplitude : ℂ) (hh : 0 < hbar) (ha : amplitude ≠ 0) (hrho : 0 < rho0)
    (hdelta : |delta| ≤ epsilon * rho0) :
    |goldenRate hbar amplitude (rho0 + delta) - goldenRate hbar amplitude rho0| /
      goldenRate hbar amplitude rho0 ≤ epsilon := by
  have hp := prefactor_positive hbar hh amplitude ha
  have he : goldenRate hbar amplitude (rho0 + delta) - goldenRate hbar amplitude rho0 =
      goldenPrefactor hbar amplitude * delta := by unfold goldenRate; ring
  rw [he, abs_mul, abs_of_pos hp]
  apply (div_le_iff₀ (rate_positive hbar rho0 hh hrho amplitude ha)).mpr
  unfold goldenRate
  calc
    goldenPrefactor hbar amplitude * |delta| ≤
        goldenPrefactor hbar amplitude * (epsilon * rho0) :=
      mul_le_mul_of_nonneg_left hdelta (le_of_lt hp)
    _ = _ := by ring

theorem rate_monotone_of_density (hbar : ℝ) (amplitude : ℂ) (rho : ℝ → ℝ)
    (hp : 0 ≤ goldenPrefactor hbar amplitude) (hrho : Monotone rho) :
    Monotone (fun phi => goldenRate hbar amplitude (rho phi)) := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (hrho hxy) hp

/-- Phenomenological counterexample; not a calculated neutron final-state density. -/
def periodicDensity (rho0 a phi : ℝ) : ℝ := rho0 * (1 + a * (1 - Real.cos phi))

theorem periodic_density_positive (rho0 a : ℝ) (hrho : 0 < rho0) (ha : 0 ≤ a)
    (phi : ℝ) : 0 < periodicDensity rho0 a phi := by
  have hc := Real.cos_le_one phi
  unfold periodicDensity
  have hn : 0 ≤ a * (1 - Real.cos phi) := mul_nonneg ha (by linarith)
  positivity

theorem density_three_values (rho0 a : ℝ) :
    periodicDensity rho0 a 0 = rho0 ∧
      periodicDensity rho0 a Real.pi = rho0 * (1 + 2 * a) ∧
      periodicDensity rho0 a (2 * Real.pi) = rho0 := by
  refine ⟨by simp [periodicDensity], ?_, by simp [periodicDensity]⟩
  simp only [periodicDensity, Real.cos_pi]
  ring

theorem density_periodic (rho0 a : ℝ) :
    Function.Periodic (periodicDensity rho0 a) (2 * Real.pi) := by
  intro phi
  simp [periodicDensity, Real.cos_add_two_pi]

theorem density_not_monotone (rho0 a : ℝ) (hrho : 0 < rho0) (ha : 0 < a) :
    ¬ Monotone (periodicDensity rho0 a) := by
  intro hm
  have hc := hm (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos])
  rw [(density_three_values rho0 a).2.1, (density_three_values rho0 a).2.2] at hc
  nlinarith [mul_pos hrho ha]

theorem rate_not_monotone (hbar rho0 a : ℝ) (amplitude : ℂ)
    (hh : 0 < hbar) (hrho : 0 < rho0) (ha : 0 < a) (hamp : amplitude ≠ 0) :
    ¬ Monotone (fun phi => goldenRate hbar amplitude (periodicDensity rho0 a phi)) := by
  intro hm
  have hc := hm (show Real.pi ≤ 2 * Real.pi by linarith [Real.pi_pos])
  unfold goldenRate at hc
  have hp := prefactor_positive hbar hh amplitude hamp
  have hd : periodicDensity rho0 a Real.pi ≤ periodicDensity rho0 a (2 * Real.pi) :=
    (mul_le_mul_iff_right₀ hp).mp hc
  rw [(density_three_values rho0 a).2.1, (density_three_values rho0 a).2.2] at hd
  nlinarith [mul_pos hrho ha]

/-- Signed effective moment/field orientation; units and radial geometry are supplied. -/
def acPhase (radius field moment hbar speed : ℝ) : ℝ :=
  2 * Real.pi * radius * field * moment / (hbar * speed ^ 2)

theorem orientation_reversal (radius field moment hbar speed : ℝ) :
    acPhase radius (-field) moment hbar speed = -acPhase radius field moment hbar speed := by
  unfold acPhase
  ring

/-- A model-specific E² bound; the periodic density is an explicit extra hypothesis,
not a density derived from weak QFT or from the ring center-of-mass spectrum. -/
theorem periodic_ac_relative_bound (hbar rho0 a radius field moment speed : ℝ)
    (amplitude : ℂ) (hh : 0 < hbar) (hM : amplitude ≠ 0) (hrho : 0 < rho0)
    (ha : 0 ≤ a) :
    |goldenRate hbar amplitude
        (periodicDensity rho0 a (acPhase radius field moment hbar speed)) -
        goldenRate hbar amplitude rho0| / goldenRate hbar amplitude rho0 ≤
      a * (acPhase radius field moment hbar speed) ^ 2 / 2 := by
  let phi := acPhase radius field moment hbar speed
  have hc : 0 ≤ 1 - Real.cos phi := sub_nonneg.mpr (Real.cos_le_one phi)
  have hcos : 1 - Real.cos phi ≤ phi ^ 2 / 2 := by
    linarith [(show 1 - phi ^ 2 / 2 ≤ Real.cos phi from Real.one_sub_sq_div_two_le_cos)]
  have hd : |rho0 * a * (1 - Real.cos phi)| ≤ (a * phi ^ 2 / 2) * rho0 := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hrho.le ha) hc)]
    nlinarith [mul_le_mul_of_nonneg_left hcos (mul_nonneg hrho.le ha)]
  have he : periodicDensity rho0 a phi = rho0 + rho0 * a * (1 - Real.cos phi) := by
    unfold periodicDensity
    ring
  change |goldenRate hbar amplitude (periodicDensity rho0 a phi) -
    goldenRate hbar amplitude rho0| / goldenRate hbar amplitude rho0 ≤ a * phi ^ 2 / 2
  rw [he]
  exact conditional_relative_rate_bound _ _ _ _ _ hh hM hrho hd

def ringLagrangian (inertia coupling omega : ℝ) : ℝ :=
  (inertia / 2) * omega ^ 2 + coupling * omega

def canonicalMomentum (inertia coupling omega : ℝ) : ℝ := inertia * omega + coupling

def ringHamiltonian (inertia coupling momentum : ℝ) : ℝ :=
  (momentum - coupling) ^ 2 / (2 * inertia)

theorem legendre_identity (inertia coupling omega : ℝ) (hI : inertia ≠ 0) :
    canonicalMomentum inertia coupling omega * omega - ringLagrangian inertia coupling omega =
      ringHamiltonian inertia coupling (canonicalMomentum inertia coupling omega) := by
  unfold canonicalMomentum ringLagrangian ringHamiltonian
  field_simp
  ring

/-- Supplied one-dimensional ring spectrum, not a QFT beta-decay Hamiltonian. -/
def ringEnergy (hbar mass radius phi : ℝ) (ell : ℤ) : ℝ :=
  hbar ^ 2 / (2 * mass * radius ^ 2) * ((ell : ℝ) - phi / (2 * Real.pi)) ^ 2

theorem flux_relabel (hbar mass radius phi : ℝ) (ell : ℤ) :
    ringEnergy hbar mass radius (phi + 2 * Real.pi) (ell + 1) =
      ringEnergy hbar mass radius phi ell := by
  unfold ringEnergy
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  push_cast
  field_simp
  ring

theorem ring_energy_nonnegative (hbar mass radius phi : ℝ) (ell : ℤ)
    (hm : 0 < mass) : 0 ≤ ringEnergy hbar mass radius phi ell := by
  unfold ringEnergy
  positivity

structure PrometheusTAKLAuditSuite : Prop where
  phase_invariance : ∀ hbar density phi amplitude,
    goldenRate hbar (unitPhase phi * amplitude) density = goldenRate hbar amplitude density
  conditional_bound : ∀ hbar rho0 delta epsilon amplitude,
    0 < hbar → amplitude ≠ 0 → 0 < rho0 → |delta| ≤ epsilon * rho0 →
    |goldenRate hbar amplitude (rho0 + delta) - goldenRate hbar amplitude rho0| /
      goldenRate hbar amplitude rho0 ≤ epsilon
  nonmonotone : ∀ rho0 a, 0 < rho0 → 0 < a → ¬ Monotone (periodicDensity rho0 a)
  spectrum_periodic : ∀ hbar mass radius phi ell,
    ringEnergy hbar mass radius (phi + 2 * Real.pi) (ell + 1) =
      ringEnergy hbar mass radius phi ell

theorem verification_suite : PrometheusTAKLAuditSuite :=
  ⟨global_phase_rate_invariant, conditional_relative_rate_bound, density_not_monotone, flux_relabel⟩
end
end PrometheusTAKLAudit

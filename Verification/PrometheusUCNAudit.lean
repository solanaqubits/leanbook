/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional UCN algebra and energy accounting

The 1/v law is an assumed cross section, not a neutron-cluster formation theorem.
The parabolic EOS is evaluated at one prescribed saturation density, with S ≥ 30;
positive energy there is not a universal no-bound-state theorem at all densities.
No exotic state, gamma channel, confinement mechanism or reactor is established.
-/
namespace PrometheusUCNAudit
noncomputable section

def crossSection (k v : ℝ) : ℝ := k / v
def reactionRate (n k v : ℝ) : ℝ := n * crossSection k v * v
def holdingProbability (n k v t : ℝ) : ℝ := 1 - Real.exp (-reactionRate n k v * t)
def slabProbability (n k L v : ℝ) : ℝ := 1 - Real.exp (-(n * k * L / v))

theorem rate_eq (n k v : ℝ) (hv : 0 < v) : reactionRate n k v = n * k := by
  unfold reactionRate crossSection
  field_simp

theorem rate_invariant (n k v₁ v₂ : ℝ) (h₁ : 0 < v₁) (h₂ : 0 < v₂) :
    reactionRate n k v₁ = reactionRate n k v₂ ∧ reactionRate n k v₁ = n * k := by
  simp [rate_eq n k v₁ h₁, rate_eq n k v₂ h₂]

theorem fixed_time_invariant (n k v₁ v₂ t : ℝ) (h₁ : 0 < v₁) (h₂ : 0 < v₂) :
    holdingProbability n k v₁ t = holdingProbability n k v₂ t := by
  simp only [holdingProbability, rate_eq n k v₁ h₁, rate_eq n k v₂ h₂]

theorem slab_eq_holding (n k L v : ℝ) (hv : 0 < v) :
    slabProbability n k L v = holdingProbability n k v (L / v) := by
  rw [slabProbability, holdingProbability, rate_eq n k v hv]
  congr 2
  ring

/-- Faster transit strictly lowers probability when all densities/scales are positive. -/
theorem slab_strict_decrease (n k L v₁ v₂ : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hL : 0 < L)
    (h₁ : 0 < v₁) (hlt : v₁ < v₂) : slabProbability n k L v₂ < slabProbability n k L v₁ := by
  have hdiv : n * k * L / v₂ < n * k * L / v₁ :=
    div_lt_div_of_pos_left (by positivity) h₁ hlt
  have hexp := Real.exp_lt_exp.mpr (neg_lt_neg hdiv)
  dsimp [slabProbability]
  linarith

/-- Counts are cast before subtraction, avoiding truncated natural subtraction. -/
def asymmetry (N Z : ℕ) : ℝ := ((N : ℝ) - Z) / ((N : ℝ) + Z)
def eosAtSaturation (S δ : ℝ) : ℝ := -16 + S * δ ^ 2

theorem neutron_asymmetry (N : ℕ) (hN : 0 < N) : asymmetry N 0 = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp [asymmetry, hn]

theorem symmetric_asymmetry (N : ℕ) : asymmetry N N = 0 := by simp [asymmetry]

theorem symmetric_energy (S : ℝ) : eosAtSaturation S 0 = -16 := by simp [eosAtSaturation]

theorem neutron_energy_lower_bound (N : ℕ) (S : ℝ) (hN : 0 < N) (hS : 30 ≤ S) :
    14 ≤ eosAtSaturation S (asymmetry N 0) ∧ 0 < eosAtSaturation S (asymmetry N 0) := by
  rw [neutron_asymmetry N hN]
  dsimp [eosAtSaturation]
  constructor <;> nlinarith

/-- All mass-energy terms must be expressed in the same unit (MeV here). -/
def qValue (N : ℕ) (neutronMass stateMass c : ℝ) : ℝ :=
  ((N : ℝ) * neutronMass - stateMass) * c ^ 2

theorem q192_iff_mass (neutronMass stateMass c : ℝ) :
    qValue 12 neutronMass stateMass c = 192 ↔
      stateMass * c ^ 2 = 12 * neutronMass * c ^ 2 - 192 := by
  unfold qValue
  norm_num
  constructor <;> intro h <;> nlinarith

/-- Exact SI elementary-charge conversion, not binary floating-point rounding. -/
def joulePerMeV : ℝ := 1602176634 / 10000000000000000000000
def hypotheticalGross : ℝ := 10000 * 16 * joulePerMeV

theorem gross_exact : hypotheticalGross = 801088317 / 31250000000000000 := by
  norm_num [hypotheticalGross, joulePerMeV]

theorem gross_bounds : 0 < hypotheticalGross ∧ hypotheticalGross < 26 / 1000000000 := by
  norm_num [hypotheticalGross, joulePerMeV]

/-- The operating input ≥ 1 J is a premise, not an inferred universal device cost. -/
theorem net_deficit (input : ℝ) (hinput : 1 ≤ input) : hypotheticalGross - input < 0 := by
  have := gross_bounds.2
  linarith

structure PrometheusUCNAuditSuite : Prop where
  invariant : ∀ n k v, 0 < v → reactionRate n k v = n * k
  slab : ∀ n k L v₁ v₂, 0 < n → 0 < k → 0 < L → 0 < v₁ → v₁ < v₂ →
    slabProbability n k L v₂ < slabProbability n k L v₁
  eos : ∀ N S, 0 < N → 30 ≤ S →
    14 ≤ eosAtSaturation S (asymmetry N 0) ∧ 0 < eosAtSaturation S (asymmetry N 0)
  mass : ∀ neutronMass stateMass c, qValue 12 neutronMass stateMass c = 192 ↔
    stateMass * c ^ 2 = 12 * neutronMass * c ^ 2 - 192
  gross : 0 < hypotheticalGross ∧ hypotheticalGross < 26 / 1000000000
  deficit : ∀ input, 1 ≤ input → hypotheticalGross - input < 0

theorem verification_suite : PrometheusUCNAuditSuite :=
  ⟨rate_eq, slab_strict_decrease, neutron_energy_lower_bound, q192_iff_mass,
    gross_bounds, net_deficit⟩
end
end PrometheusUCNAudit

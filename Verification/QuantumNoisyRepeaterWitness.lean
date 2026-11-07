/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumScheduledNoisyRepeater

/-! Kernel-checked rational interval certificates for a fixed noisy schedule.
Minimal depths refer to the specified first input and the output of depth 16 at
the first level. They do not imply global optimality among all schedules. -/
noncomputable section
namespace QuantumNoisyRepeaterWitness
open QuantumScheduledNoisyRepeater QuantumNoisyBBPSSWTree QuantumNoisyBBPSSW
open QuantumNoisyBBPSSWConvergence QuantumNestedRepeater QuantumHeterogeneousBBPSSW
open QuantumBBPSSWDistillation QuantumBBPSSWConvergence QuantumCentralDepolarization
open QuantumNoisyVisibility QuantumEntanglementSwappingPurificationContract
open scoped BigOperators ComplexOrder Matrix Kronecker

def witnessGamma : Visibility := ⟨19 / 20, by norm_num, by norm_num⟩
def witnessInitialVisibility : Visibility := ⟨4 / 5, by norm_num, by norm_num⟩
def witnessSchedule : List ℕ := [16, 16]
def firstLevelVisibility : Visibility :=
  scheduledVisibility witnessGamma witnessInitialVisibility [16]
def secondLevelVisibility : Visibility :=
  scheduledVisibility witnessGamma witnessInitialVisibility [16, 16]

theorem noisyRecurrence_mono_of_ge_quarter {γ x y : ℝ}
    (hγ : 0 ≤ γ) (hx : 1 / 4 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    noisyRecurrence γ x ≤ noisyRecurrence γ y := by
  have h := recurrence_strictMonoOn.monotoneOn ⟨hx, le_trans hxy hy⟩
    ⟨le_trans hx hxy, hy⟩ hxy
  exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left h hγ)

/-- Both endpoint transitions are verified inequalities; no rounded result is assumed. -/
theorem noisyOrbit_interval_step (γ : Visibility) {F a b c d : ℝ} {n : ℕ}
    (hF : 1 / 4 ≤ F ∧ F ≤ 1)
    (h : a ≤ noisyOrbit γ.val F n ∧ noisyOrbit γ.val F n ≤ b)
    (ha : 1 / 4 ≤ a) (hb : b ≤ 1)
    (hc : c ≤ noisyRecurrence γ.val a) (hd : noisyRecurrence γ.val b ≤ d) :
    c ≤ noisyOrbit γ.val F (n+1) ∧ noisyOrbit γ.val F (n+1) ≤ d := by
  have hf := noisyOrbit_quarter_bounds γ hF n
  rw [noisyOrbit_succ]
  exact ⟨le_trans hc (noisyRecurrence_mono_of_ge_quarter γ.nonnegative ha h.1 hf.2),
    le_trans (noisyRecurrence_mono_of_ge_quarter γ.nonnegative hf.1 h.2 hb) hd⟩

theorem first_orbit_certificate :
    (84911037 / 100000000 ≤ noisyOrbit (19 / 20) (73 / 100) 15 ∧
      noisyOrbit (19 / 20) (73 / 100) 15 ≤ 21227761 / 25000000) ∧
    (85169269 / 100000000 ≤ noisyOrbit (19 / 20) (73 / 100) 16 ∧
      noisyOrbit (19 / 20) (73 / 100) 16 ≤ 3406771 / 4000000) := by
  have hF : 1 / 4 ≤ (73 / 100 : ℝ) ∧ (73 / 100 : ℝ) ≤ 1 := by norm_num
  have h0 : 73 / 100 ≤ noisyOrbit witnessGamma.val (73 / 100) 0 ∧
      noisyOrbit witnessGamma.val (73 / 100) 0 ≤ 73 / 100 := by norm_num
  have h1 : 18542849 / 25000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 1 ∧
      noisyOrbit witnessGamma.val (73 / 100) 1 ≤ 74171397 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h0 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h2 : 15067769 / 20000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 2 ∧
      noisyOrbit witnessGamma.val (73 / 100) 2 ≤ 75338847 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h1 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h3 : 19121127 / 25000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 3 ∧
      noisyOrbit witnessGamma.val (73 / 100) 3 ≤ 76484511 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h2 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h4 : 15518219 / 20000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 4 ∧
      noisyOrbit witnessGamma.val (73 / 100) 4 ≤ 77591099 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h3 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h5 : 39321503 / 50000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 5 ∧
      noisyOrbit witnessGamma.val (73 / 100) 5 ≤ 78643011 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h4 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h6 : 796273 / 1000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 6 ∧
      noisyOrbit witnessGamma.val (73 / 100) 6 ≤ 15925461 / 20000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h5 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h7 : 16106873 / 20000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 7 ∧
      noisyOrbit witnessGamma.val (73 / 100) 7 ≤ 80534371 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h6 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h8 : 81358217 / 100000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 8 ∧
      noisyOrbit witnessGamma.val (73 / 100) 8 ≤ 81358223 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h7 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h9 : 82096417 / 100000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 9 ∧
      noisyOrbit witnessGamma.val (73 / 100) 9 ≤ 82096423 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h8 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h10 : 20687423 / 25000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 10 ∧
      noisyOrbit witnessGamma.val (73 / 100) 10 ≤ 41374849 / 50000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h9 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h11 : 41660673 / 50000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 11 ∧
      noisyOrbit witnessGamma.val (73 / 100) 11 ≤ 10415169 / 12500000 := by
    apply noisyOrbit_interval_step witnessGamma hF h10 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h12 : 83816587 / 100000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 12 ∧
      noisyOrbit witnessGamma.val (73 / 100) 12 ≤ 41908297 / 50000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h11 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h13 : 84241861 / 100000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 13 ∧
      noisyOrbit witnessGamma.val (73 / 100) 13 ≤ 21060467 / 25000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h12 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h14 : 42302129 / 50000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 14 ∧
      noisyOrbit witnessGamma.val (73 / 100) 14 ≤ 16920853 / 20000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h13 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h15 : 84911037 / 100000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 15 ∧
      noisyOrbit witnessGamma.val (73 / 100) 15 ≤ 21227761 / 25000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h14 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h16 : 85169269 / 100000000 ≤ noisyOrbit witnessGamma.val (73 / 100) 16 ∧
      noisyOrbit witnessGamma.val (73 / 100) 16 ≤ 3406771 / 4000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h15 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  exact ⟨h15, h16⟩

theorem second_orbit_certificate {F : ℝ}
    (hinit : 73271197 / 100000000 ≤ F ∧ F ≤ 73271247 / 100000000) :
    (84975023 / 100000000 ≤ noisyOrbit (19 / 20) F 15 ∧
      noisyOrbit (19 / 20) F 15 ≤ 265547 / 312500) ∧
    (85222959 / 100000000 ≤ noisyOrbit (19 / 20) F 16 ∧
      noisyOrbit (19 / 20) F 16 ≤ 3408919 / 4000000) := by
  have hF : 1 / 4 ≤ F ∧ F ≤ 1 := by constructor <;> linarith [hinit.1, hinit.2]
  have h0 : 73271197 / 100000000 ≤ noisyOrbit witnessGamma.val F 0 ∧
      noisyOrbit witnessGamma.val F 0 ≤ 73271247 / 100000000 := hinit
  have h1 : 74443253 / 100000000 ≤ noisyOrbit witnessGamma.val F 1 ∧
      noisyOrbit witnessGamma.val F 1 ≤ 9305413 / 12500000 := by
    apply noisyOrbit_interval_step witnessGamma hF h0 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h2 : 18901809 / 25000000 ≤ noisyOrbit witnessGamma.val F 2 ∧
      noisyOrbit witnessGamma.val F 2 ≤ 75607287 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h1 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h3 : 7674533 / 10000000 ≤ noisyOrbit witnessGamma.val F 3 ∧
      noisyOrbit witnessGamma.val F 3 ≤ 3837269 / 5000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h2 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h4 : 77840539 / 100000000 ≤ noisyOrbit witnessGamma.val F 4 ∧
      noisyOrbit witnessGamma.val F 4 ≤ 77840587 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h3 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h5 : 39438901 / 50000000 ≤ noisyOrbit witnessGamma.val F 5 ∧
      noisyOrbit witnessGamma.val F 5 ≤ 9859731 / 12500000 := by
    apply noisyOrbit_interval_step witnessGamma hF h4 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h6 : 9980613 / 12500000 ≤ noisyOrbit witnessGamma.val F 6 ∧
      noisyOrbit witnessGamma.val F 6 ≤ 79844947 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h5 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h7 : 80733063 / 100000000 ≤ noisyOrbit witnessGamma.val F 7 ∧
      noisyOrbit witnessGamma.val F 7 ≤ 80733103 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h6 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h8 : 5096071 / 6250000 ≤ noisyOrbit witnessGamma.val F 8 ∧
      noisyOrbit witnessGamma.val F 8 ≤ 81537173 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h7 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h9 : 82255463 / 100000000 ≤ noisyOrbit witnessGamma.val F 9 ∧
      noisyOrbit witnessGamma.val F 9 ≤ 82255497 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h8 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h10 : 41444713 / 50000000 ≤ noisyOrbit witnessGamma.val F 10 ∧
      noisyOrbit witnessGamma.val F 10 ≤ 82889457 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h9 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h11 : 5215177 / 6250000 ≤ noisyOrbit witnessGamma.val F 11 ∧
      noisyOrbit witnessGamma.val F 11 ≤ 4172143 / 5000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h10 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h12 : 41960617 / 50000000 ≤ noisyOrbit witnessGamma.val F 12 ∧
      noisyOrbit witnessGamma.val F 12 ≤ 83921259 / 100000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h11 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h13 : 3373251 / 4000000 ≤ noisyOrbit witnessGamma.val F 13 ∧
      noisyOrbit witnessGamma.val F 13 ≤ 42165649 / 50000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h12 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h14 : 21170031 / 25000000 ≤ noisyOrbit witnessGamma.val F 14 ∧
      noisyOrbit witnessGamma.val F 14 ≤ 5292509 / 6250000 := by
    apply noisyOrbit_interval_step witnessGamma hF h13 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h15 : 84975023 / 100000000 ≤ noisyOrbit witnessGamma.val F 15 ∧
      noisyOrbit witnessGamma.val F 15 ≤ 265547 / 312500 := by
    apply noisyOrbit_interval_step witnessGamma hF h14 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  have h16 : 85222959 / 100000000 ≤ noisyOrbit witnessGamma.val F 16 ∧
      noisyOrbit witnessGamma.val F 16 ≤ 3408919 / 4000000 := by
    apply noisyOrbit_interval_step witnessGamma hF h15 <;>
      norm_num [witnessGamma, noisyRecurrence, recurrence, targetMass, successProbability]
  exact ⟨h15, h16⟩

theorem initial_swap_fidelity : swapFidelity witnessInitialVisibility.val = 73 / 100 := by
  norm_num [swapFidelity, witnessInitialVisibility]

theorem first_level_value (m : ℕ) :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [m] =
      (4 * noisyOrbit (19 / 20) (73 / 100) m - 1) / 3 := by
  change noisyLevelVisibilityValue witnessGamma m witnessInitialVisibility.val = _
  unfold noisyLevelVisibilityValue
  rw [initial_swap_fidelity]
  rfl

theorem second_level_value (m : ℕ) :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, m] =
      (4 * noisyOrbit (19 / 20) (swapFidelity firstLevelVisibility.val) m - 1) / 3 := rfl

theorem first_level_visibility_bounds :
    8022568 / 10000000 ≤ firstLevelVisibility.val ∧
    firstLevelVisibility.val ≤ 8022572 / 10000000 := by
  have h := first_orbit_certificate.2
  change 8022568 / 10000000 ≤ scheduledVisibilityValue _ _ [16] ∧
    scheduledVisibilityValue _ _ [16] ≤ 8022572 / 10000000
  rw [first_level_value]
  constructor <;> linarith [h.1, h.2]

theorem second_swap_fidelity_bounds :
    73271197 / 100000000 ≤ swapFidelity firstLevelVisibility.val ∧
    swapFidelity firstLevelVisibility.val ≤ 73271247 / 100000000 := by
  have h := first_level_visibility_bounds
  unfold swapFidelity
  constructor <;> nlinarith [h.1, h.2]

theorem second_level_visibility_bounds :
    8029727 / 10000000 ≤ secondLevelVisibility.val ∧
    secondLevelVisibility.val ≤ 8029731 / 10000000 := by
  have h := (second_orbit_certificate second_swap_fidelity_bounds).2
  change 8029727 / 10000000 ≤ scheduledVisibilityValue _ _ [16, 16] ∧
    scheduledVisibilityValue _ _ [16, 16] ≤ 8029731 / 10000000
  rw [second_level_value]
  constructor <;> linarith [h.1, h.2]

theorem first_level_depth_15_lt_initial :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [15] < 4 / 5 := by
  rw [first_level_value]
  linarith [first_orbit_certificate.1.2]

theorem first_level_depth_16_gt_initial : (4 / 5 : ℝ) < firstLevelVisibility.val := by
  linarith [first_level_visibility_bounds.1]

theorem second_level_depth_15_lt_initial :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, 15] < 4 / 5 := by
  rw [second_level_value]
  linarith [(second_orbit_certificate second_swap_fidelity_bounds).1.2]

theorem second_level_depth_15_lt_first :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, 15] <
      firstLevelVisibility.val :=
  lt_trans second_level_depth_15_lt_initial first_level_depth_16_gt_initial

theorem second_level_depth_16_gt_first : firstLevelVisibility.val < secondLevelVisibility.val := by
  linarith [first_level_visibility_bounds.2, second_level_visibility_bounds.1]

/-- Both actual swapped inputs are well inside the same supercritical working window. -/
theorem witness_swap_inside_window {w : ℝ} (h : 4 / 5 ≤ w ∧ w ≤ 81 / 100) :
    lowerWindowBound (19 / 20) < swapFidelity w ∧
    swapFidelity w < upperWindowCeiling (19 / 20) := by
  have hn := Real.sqrt_nonneg (noisyDiscFactor (19 / 20))
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 31 by norm_num)
  have h31 := Real.sqrt_nonneg (31:ℝ)
  have hw2 : w^2 ≤ (81 / 100 : ℝ)^2 :=
    pow_le_pow_left₀ (by linarith [h.1]) h.2 2
  have hr : 5 < Real.sqrt (31:ℝ) := by nlinarith
  constructor
  · unfold lowerWindowBound swapFidelity
    nlinarith [h.1, h.2]
  · rw [nineteen_twentieths_ceiling]
    unfold swapFidelity
    nlinarith [hw2, hr]

theorem first_level_minimal_depth_16 {m : ℕ} (hm : m < 16) :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [m] < 4 / 5 := by
  have hw := witness_swap_inside_window (w := (4 / 5)) ⟨le_rfl, by norm_num⟩
  norm_num [swapFidelity] at hw
  have hmono := (noisyOrbit_strictMono_inside_window nineteen_twentieths_above_critical
    (by norm_num) hw.1 hw.2).monotone (show m ≤ 15 by omega)
  rw [first_level_value]
  linarith [first_orbit_certificate.1.2]

theorem second_level_minimal_depth_16 {m : ℕ} (hm : m < 16) :
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, m] <
      firstLevelVisibility.val := by
  have hw := witness_swap_inside_window (w := firstLevelVisibility.val)
    ⟨first_level_depth_16_gt_initial.le, by linarith [first_level_visibility_bounds.2]⟩
  have hmono := (noisyOrbit_strictMono_inside_window nineteen_twentieths_above_critical
    (by norm_num) hw.1 hw.2).monotone (show m ≤ 15 by omega)
  rw [second_level_value]
  have hb := (second_orbit_certificate second_swap_fidelity_bounds).1.2
  linarith [first_level_depth_16_gt_initial]

theorem witnessSchedule_localQualityGain :
    LocalQualityGain witnessGamma witnessInitialVisibility witnessSchedule := by
  intro pref m suffix he
  rcases pref with _ | ⟨a, pref⟩
  · have hm : m = 16 := by simpa [witnessSchedule] using congrArg List.head? he.symm
    subst m
    exact first_level_depth_16_gt_initial.le
  · rcases pref with _ | ⟨b, pref⟩
    · have ha : a = 16 := by simpa [witnessSchedule] using congrArg List.head? he.symm
      subst a
      have hm : m = 16 := by
        simpa [witnessSchedule] using congrArg (fun l => l.tail.head?) he.symm
      subst m
      exact second_level_depth_16_gt_first.le
    · have hl := congrArg List.length he
      simp [witnessSchedule] at hl

theorem witnessSchedule_sustains_initial_quality :
    (4 / 5 : ℝ) < scheduledVisibilityValue witnessGamma witnessInitialVisibility [16] ∧
    (4 / 5 : ℝ) < scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, 16] :=
  ⟨first_level_depth_16_gt_initial,
    lt_trans first_level_depth_16_gt_initial second_level_depth_16_gt_first⟩

theorem witnessSchedule_refinement_and_psd :
    scheduledRepeaterMatrix witnessGamma witnessInitialVisibility witnessSchedule =
      (scheduledRepeaterProbability witnessGamma witnessInitialVisibility witnessSchedule : ℂ) •
        isotropic secondLevelVisibility ∧
    (scheduledRepeaterMatrix witnessGamma witnessInitialVisibility witnessSchedule).PosSemidef ∧
    0 < scheduledRepeaterProbability witnessGamma witnessInitialVisibility witnessSchedule ∧
    scheduledRepeaterProbability witnessGamma witnessInitialVisibility witnessSchedule ≤ 1 :=
  ⟨scheduledRepeaterMatrix_refinement _ _ _, scheduledRepeaterMatrix_posSemidef _ _ _,
    scheduledRepeaterProbability_pos _ _ _, scheduledRepeaterProbability_le_one _ _ _⟩

theorem witnessSchedule_trace :
    (scheduledRepeaterMatrix witnessGamma witnessInitialVisibility witnessSchedule).trace =
      (scheduledRepeaterProbability witnessGamma witnessInitialVisibility witnessSchedule : ℂ) :=
  scheduledRepeaterMatrix_trace _ _ _

theorem witnessSchedule_conditional :
    (scheduledRepeaterProbability witnessGamma witnessInitialVisibility witnessSchedule : ℂ)⁻¹ •
      scheduledRepeaterMatrix witnessGamma witnessInitialVisibility witnessSchedule =
      isotropic secondLevelVisibility := scheduledRepeaterMatrix_conditional _ _ _

theorem witnessSchedule_conditional_density :
    (isotropic secondLevelVisibility).PosSemidef ∧ (isotropic secondLevelVisibility).trace = 1 :=
  ⟨QuantumBellDiagonalInputs.density_positive _, isotropic_trace _⟩

theorem witnessSchedule_resource_count :
    scheduledSegmentCount witnessSchedule = 4 ∧
    scheduledRawPairCount witnessSchedule = 2^34 ∧
    scheduledRawPairCount witnessSchedule = 17179869184 := by
  norm_num [witnessSchedule, scheduledSegmentCount, scheduledRawPairCount]

structure QuantumNoisyRepeaterWitnessSuite : Prop where
  gain : LocalQualityGain witnessGamma witnessInitialVisibility witnessSchedule
  first_minimal : ∀ m < 16,
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [m] < 4 / 5
  second_minimal : ∀ m < 16,
    scheduledVisibilityValue witnessGamma witnessInitialVisibility [16, m] <
      firstLevelVisibility.val
  resources : scheduledRawPairCount witnessSchedule = 17179869184

theorem verification_suite : QuantumNoisyRepeaterWitnessSuite :=
  ⟨witnessSchedule_localQualityGain, fun _ => first_level_minimal_depth_16,
    fun _ => second_level_minimal_depth_16, witnessSchedule_resource_count.2.2⟩

end QuantumNoisyRepeaterWitness

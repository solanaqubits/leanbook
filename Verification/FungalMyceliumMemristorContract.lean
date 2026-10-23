/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Prescribed bounded conductance and spatial attenuation

The voltage thresholds are active; the strict interior retains its state.
Noncommuting updates establish history dependence in this discrete model.
The spike threshold is strict. Attenuation is indexed by spatial steps, not time.
No calibrated fungal physiology, autonomous oscillation or network safety is claimed.
-/
namespace FungalMyceliumMemristorContract

structure MemristorParameters where
  Gmin : ℚ
  Gmax : ℚ
  Vth : ℚ
  alphaUp : ℚ
  alphaDown : ℚ
  h_Gmin_pos : 0 < Gmin
  h_Gmin_lt_Gmax : Gmin < Gmax
  h_Vth_pos : 0 < Vth
  h_alphaUp_pos : 0 < alphaUp
  h_alphaUp_le_one : alphaUp ≤ 1
  h_alphaDown_pos : 0 < alphaDown
  h_alphaDown_le_one : alphaDown ≤ 1

@[ext] structure MemristorState (p : MemristorParameters) where
  conductance : ℚ
  h_min : p.Gmin ≤ conductance
  h_max : conductance ≤ p.Gmax

abbrev MyceliumNodeState := MemristorState

def upStep {p : MemristorParameters} (s : MemristorState p) : MemristorState p where
  conductance := s.conductance + p.alphaUp * (p.Gmax - s.conductance)
  h_min := by
    have := mul_nonneg p.h_alphaUp_pos.le (sub_nonneg.mpr s.h_max)
    linarith [s.h_min]
  h_max := by
    have := mul_nonneg (sub_nonneg.mpr p.h_alphaUp_le_one) (sub_nonneg.mpr s.h_max)
    nlinarith

def downStep {p : MemristorParameters} (s : MemristorState p) : MemristorState p where
  conductance := s.conductance - p.alphaDown * (s.conductance - p.Gmin)
  h_min := by
    have := mul_nonneg (sub_nonneg.mpr p.h_alphaDown_le_one) (sub_nonneg.mpr s.h_min)
    nlinarith
  h_max := by
    have := mul_nonneg p.h_alphaDown_pos.le (sub_nonneg.mpr s.h_min)
    linarith [s.h_max]

def memristorStep {p : MemristorParameters} (s : MemristorState p) (V : ℚ) :
    MemristorState p :=
  if p.Vth ≤ V then upStep s else if V ≤ -p.Vth then downStep s else s

theorem conductance_bounds_invariant {p : MemristorParameters} (s : MemristorState p)
    (V : ℚ) : p.Gmin ≤ (memristorStep s V).conductance ∧
      (memristorStep s V).conductance ≤ p.Gmax :=
  ⟨(memristorStep s V).h_min, (memristorStep s V).h_max⟩

theorem potentiation_monotonicity {p : MemristorParameters} (s : MemristorState p) :
    s.conductance ≤ (upStep s).conductance := by
  exact le_add_of_nonneg_right
    (mul_nonneg p.h_alphaUp_pos.le (sub_nonneg.mpr s.h_max))

theorem depression_monotonicity {p : MemristorParameters} (s : MemristorState p) :
    (downStep s).conductance ≤ s.conductance := by
  exact sub_le_self _ (mul_nonneg p.h_alphaDown_pos.le (sub_nonneg.mpr s.h_min))

theorem potentiation_strict {p : MemristorParameters} (s : MemristorState p)
    (hs : s.conductance < p.Gmax) : s.conductance < (upStep s).conductance :=
  lt_add_of_pos_right _ (mul_pos p.h_alphaUp_pos (sub_pos.mpr hs))

theorem depression_strict {p : MemristorParameters} (s : MemristorState p)
    (hs : p.Gmin < s.conductance) : (downStep s).conductance < s.conductance :=
  sub_lt_self _ (mul_pos p.h_alphaDown_pos (sub_pos.mpr hs))

theorem subthreshold_invariance {p : MemristorParameters} (s : MemristorState p)
    (V : ℚ) (hV : |V| < p.Vth) : memristorStep s V = s := by
  have h := abs_lt.mp hV
  simp [memristorStep, not_le.mpr h.2, not_le.mpr h.1]

theorem zero_voltage_identity {p : MemristorParameters} (s : MemristorState p) :
    memristorStep s 0 = s :=
  subthreshold_invariance s 0 (by simpa using p.h_Vth_pos)

theorem positive_threshold_active {p : MemristorParameters} (s : MemristorState p) :
    memristorStep s p.Vth = upStep s := by simp [memristorStep]

theorem negative_threshold_active {p : MemristorParameters} (s : MemristorState p) :
    memristorStep s (-p.Vth) = downStep s := by
  have h : ¬ p.Vth ≤ -p.Vth := by linarith [p.h_Vth_pos]
  simp [memristorStep, h]

theorem positive_drive_monotonicity {p : MemristorParameters} (s : MemristorState p)
    (V : ℚ) (hV : p.Vth ≤ V) : s.conductance ≤ (memristorStep s V).conductance := by
  simpa [memristorStep, hV] using potentiation_monotonicity s

theorem negative_drive_monotonicity {p : MemristorParameters} (s : MemristorState p)
    (V : ℚ) (hV : V ≤ -p.Vth) : (memristorStep s V).conductance ≤ s.conductance := by
  have h : ¬ p.Vth ≤ V := by linarith [p.h_Vth_pos]
  simpa [memristorStep, h, hV] using depression_monotonicity s

theorem hysteresis_monotonicity_up {p : MemristorParameters} (s : MyceliumNodeState p)
    (V : ℚ) (hV : p.Vth ≤ V) : s.conductance ≤ (memristorStep s V).conductance :=
  positive_drive_monotonicity s V hV

theorem hysteresis_monotonicity_down {p : MemristorParameters} (s : MyceliumNodeState p)
    (V : ℚ) (hV : V ≤ -p.Vth) : (memristorStep s V).conductance ≤ s.conductance :=
  negative_drive_monotonicity s V hV

theorem subthreshold_stability {p : MemristorParameters} (s : MyceliumNodeState p)
    (V : ℚ) (hV : |V| < p.Vth) : memristorStep s V = s :=
  subthreshold_invariance s V hV

theorem history_difference {p : MemristorParameters} (s : MemristorState p) :
    (upStep (downStep s)).conductance - (downStep (upStep s)).conductance =
      p.alphaUp * p.alphaDown * (p.Gmax - p.Gmin) := by
  simp only [upStep, downStep]
  ring

theorem history_dependence {p : MemristorParameters} (s : MemristorState p) :
    (downStep (upStep s)).conductance < (upStep (downStep s)).conductance := by
  have h := mul_pos (mul_pos p.h_alphaUp_pos p.h_alphaDown_pos)
    (sub_pos.mpr p.h_Gmin_lt_Gmax)
  rw [← history_difference s] at h
  linarith

theorem threshold_history_dependence {p : MemristorParameters} (s : MemristorState p) :
    (memristorStep (memristorStep s p.Vth) (-p.Vth)).conductance <
      (memristorStep (memristorStep s (-p.Vth)) p.Vth).conductance := by
  simp only [positive_threshold_active, negative_threshold_active]
  exact history_dependence s

def current {p : MemristorParameters} (s : MemristorState p) (V : ℚ) : ℚ :=
  s.conductance * V

/-- The same positive inactive probe retains the different histories and orders current. -/
theorem common_probe_history {p : MemristorParameters} (s : MemristorState p)
    (V : ℚ) (hV0 : 0 < V) (hVth : V < p.Vth) :
    memristorStep (downStep (upStep s)) V = downStep (upStep s) ∧
    memristorStep (upStep (downStep s)) V = upStep (downStep s) ∧
    current (memristorStep (downStep (upStep s)) V) V <
      current (memristorStep (upStep (downStep s)) V) V := by
  have hV : |V| < p.Vth := by rwa [abs_of_pos hV0]
  have hd := subthreshold_invariance (downStep (upStep s)) V hV
  have hu := subthreshold_invariance (upStep (downStep s)) V hV
  refine ⟨hd, hu, ?_⟩
  rw [hd, hu]
  exact mul_lt_mul_of_pos_right (history_dependence s) hV0

def power {p : MemristorParameters} (s : MemristorState p) (V : ℚ) : ℚ :=
  s.conductance * V ^ 2

theorem power_eq_current_voltage {p : MemristorParameters} (s : MemristorState p)
    (V : ℚ) : power s V = current s V * V := by unfold power current; ring

theorem power_nonnegative {p : MemristorParameters} (s : MemristorState p) (V : ℚ) :
    0 ≤ power s V := mul_nonneg (p.h_Gmin_pos.le.trans s.h_min) (sq_nonneg V)

def spikeGenerator (Sth S : ℚ) : Bool := decide (Sth < S)

theorem spike_iff (Sth S : ℚ) : spikeGenerator Sth S = true ↔ Sth < S := by
  simp [spikeGenerator]

theorem spike_threshold_inactive (Sth : ℚ) : spikeGenerator Sth Sth = false := by
  simp [spikeGenerator]

theorem spike_zero_inactive (Sth : ℚ) (hSth : 0 < Sth) :
    spikeGenerator Sth 0 = false := by simp [spikeGenerator, not_lt.mpr hSth.le]

theorem spike_noise_margin (Sth S δ : ℚ) (h : S + |δ| ≤ Sth) :
    spikeGenerator Sth (S + δ) = false := by
  have hle : S + δ ≤ Sth := by linarith [le_abs_self δ]
  simp [spikeGenerator, not_lt.mpr hle]

def spatialAmplitude (A0 γ : ℚ) (x : ℕ) : ℚ := A0 * γ ^ x

theorem spatial_amplitude_bounds (A0 γ : ℚ) (x : ℕ) (hA : 0 ≤ A0)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 ≤ spatialAmplitude A0 γ x ∧ spatialAmplitude A0 γ x ≤ A0 := by
  exact ⟨mul_nonneg hA (pow_nonneg hγ0.le x),
    by simpa [spatialAmplitude] using
      mul_le_mul_of_nonneg_left (pow_le_one₀ hγ0.le hγ1.le (n := x)) hA⟩

theorem spatial_strict_decay (A0 γ : ℚ) (hA : 0 < A0)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : StrictAnti (spatialAmplitude A0 γ) := by
  intro x y hxy
  exact mul_lt_mul_of_pos_left (pow_right_strictAnti₀ hγ0 hγ1 hxy) hA

theorem spatial_successor_strict_decay (A0 γ : ℚ) (x : ℕ) (hA : 0 < A0)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    spatialAmplitude A0 γ (x + 1) < spatialAmplitude A0 γ x :=
  spatial_strict_decay A0 γ hA hγ0 hγ1 (Nat.lt_succ_self x)

theorem finite_chain_attenuation (A0 γ : ℚ) (L x : ℕ) (hx : x ≤ L)
    (hA : 0 < A0) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    spatialAmplitude A0 γ L ≤ spatialAmplitude A0 γ x :=
  (spatial_strict_decay A0 γ hA hγ0 hγ1).antitone hx

theorem spatial_attenuation_decay (A0 γ : ℚ) (hA : 0 < A0)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) : StrictAnti (spatialAmplitude A0 γ) :=
  spatial_strict_decay A0 γ hA hγ0 hγ1

theorem spatial_attenuation_bound (A0 γ : ℚ) (x : ℕ) (hA : 0 ≤ A0)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    0 ≤ spatialAmplitude A0 γ x ∧ spatialAmplitude A0 γ x ≤ A0 :=
  spatial_amplitude_bounds A0 γ x hA hγ0 hγ1

structure FungalMyceliumMemristorSuite : Prop where
  bounds : ∀ (p : MemristorParameters) (s : MemristorState p) (V : ℚ),
    p.Gmin ≤ (memristorStep s V).conductance ∧ (memristorStep s V).conductance ≤ p.Gmax
  potentiation : ∀ (p : MemristorParameters) (s : MemristorState p),
    s.conductance ≤ (upStep s).conductance
  depression : ∀ (p : MemristorParameters) (s : MemristorState p),
    (downStep s).conductance ≤ s.conductance
  active_up : ∀ (p : MemristorParameters) (s : MemristorState p) (V : ℚ),
    p.Vth ≤ V → s.conductance ≤ (memristorStep s V).conductance
  active_down : ∀ (p : MemristorParameters) (s : MemristorState p) (V : ℚ),
    V ≤ -p.Vth → (memristorStep s V).conductance ≤ s.conductance
  threshold_endpoints : ∀ (p : MemristorParameters) (s : MemristorState p),
    memristorStep s p.Vth = upStep s ∧ memristorStep s (-p.Vth) = downStep s
  retention : ∀ (p : MemristorParameters) (s : MemristorState p) (V : ℚ),
    |V| < p.Vth → memristorStep s V = s
  history : ∀ (p : MemristorParameters) (s : MemristorState p),
    (downStep (upStep s)).conductance < (upStep (downStep s)).conductance
  common_probe : ∀ (p : MemristorParameters) (s : MemristorState p) (V : ℚ),
    0 < V → V < p.Vth →
    memristorStep (downStep (upStep s)) V = downStep (upStep s) ∧
    memristorStep (upStep (downStep s)) V = upStep (downStep s) ∧
    current (memristorStep (downStep (upStep s)) V) V <
      current (memristorStep (upStep (downStep s)) V) V
  passive_power : ∀ (p : MemristorParameters) (s : MemristorState p) (V : ℚ), 0 ≤ power s V
  spike_characterization : ∀ (Sth S : ℚ), spikeGenerator Sth S = true ↔ Sth < S
  spike_zero : ∀ (Sth : ℚ), 0 < Sth → spikeGenerator Sth 0 = false
  spatial_bounds : ∀ (A0 γ : ℚ) (x : ℕ), 0 ≤ A0 → 0 < γ → γ < 1 →
    0 ≤ spatialAmplitude A0 γ x ∧ spatialAmplitude A0 γ x ≤ A0
  spatial_decay : ∀ (A0 γ : ℚ), 0 < A0 → 0 < γ → γ < 1 →
    StrictAnti (spatialAmplitude A0 γ)

theorem verification_suite : FungalMyceliumMemristorSuite := {
  bounds := fun _ => conductance_bounds_invariant
  potentiation := fun _ => potentiation_monotonicity
  depression := fun _ => depression_monotonicity
  active_up := fun _ => hysteresis_monotonicity_up
  active_down := fun _ => hysteresis_monotonicity_down
  threshold_endpoints := fun _ s =>
    ⟨positive_threshold_active s, negative_threshold_active s⟩
  retention := fun _ => subthreshold_invariance
  history := fun _ => history_dependence
  common_probe := fun _ => common_probe_history
  passive_power := fun _ => power_nonnegative
  spike_characterization := spike_iff
  spike_zero := spike_zero_inactive
  spatial_bounds := spatial_amplitude_bounds
  spatial_decay := spatial_strict_decay
}

end FungalMyceliumMemristorContract

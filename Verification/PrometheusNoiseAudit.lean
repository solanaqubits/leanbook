/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional stopping, coincidence probabilities and distinct error denominators

The constant-coefficient CSDA model is deterministic. Stochastic radiative losses,
neutrino-induced local muons and detector backgrounds are outside its conclusion.
Probability factorization is an explicit premise, never inferred from pC = 0.
Window accumulation requires independent identically distributed windows; its
formula below is a scalar model, not a proof that dead-time windows are independent.
-/
namespace PrometheusNoiseAudit
noncomputable section

/-- Homogeneous mass thickness: density in g/cm³ and length in cm. -/
def massThickness (density length : ℝ) : ℝ := density * length

/-- Signal and background shielding paths are independent inputs. -/
structure Geometry where
  signalChord : ℝ
  shieldLength : ℝ → ℝ
  signal_nonneg : 0 ≤ signalChord
  shield_nonneg : ∀ θ, 0 ≤ shieldLength θ

def shieldThickness (g : Geometry) (density θ : ℝ) : ℝ :=
  massThickness density (g.shieldLength θ)

theorem shield_thickness_nonneg (g : Geometry) (density θ : ℝ) (hρ : 0 ≤ density) :
    0 ≤ shieldThickness g density θ := mul_nonneg hρ (g.shield_nonneg θ)

/-- Integrated range for -dE/dX = a + b E before stopping, a,b > 0. -/
def stoppingRange (a b E : ℝ) : ℝ := Real.log (1 + b / a * E) / b

/-- Continue by zero after stopping; negative kinetic energy is excluded. -/
def residualEnergy (a b E X : ℝ) : ℝ :=
  max 0 ((E + a / b) * Real.exp (-b * X) - a / b)

theorem residual_initial (a b E : ℝ) (hE : 0 ≤ E) : residualEnergy a b E 0 = E := by
  simp [residualEnergy, max_eq_right hE]

theorem stopping_range_pos (a b E : ℝ) (ha : 0 < a) (hb : 0 < b) (hE : 0 < E) :
    0 < stoppingRange a b E := by
  apply div_pos _ hb
  apply Real.log_pos
  have := mul_pos (div_pos hb ha) hE
  linarith

theorem range_mono (a b E Ecut : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hE : 0 ≤ E) (hcut : E ≤ Ecut) : stoppingRange a b E ≤ stoppingRange a b Ecut := by
  apply (div_le_div_iff_of_pos_right hb).2
  apply Real.log_le_log
  · have := mul_nonneg (div_pos hb ha).le hE
    linarith
  · exact add_le_add_right (mul_le_mul_of_nonneg_left hcut (div_pos hb ha).le) 1

theorem residual_zero_at_or_after_range (a b E X : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hE : 0 < E)
    (hX : stoppingRange a b E ≤ X) : residualEnergy a b E X = 0 := by
  have harg : 0 < 1 + b / a * E := by positivity
  have hprod : 0 < E + a / b := by positivity
  have hexp : Real.exp (-b * X) ≤ (1 + b / a * E)⁻¹ := by
    calc
      Real.exp (-b * X) ≤ Real.exp (-Real.log (1 + b / a * E)) := by
        apply Real.exp_le_exp.mpr
        dsimp [stoppingRange] at hX
        have h := (div_le_iff₀ hb).mp hX
        nlinarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log harg]
  have heq : (E + a / b) * (1 + b / a * E)⁻¹ = a / b := by
    field_simp
    ring
  unfold residualEnergy
  apply max_eq_left
  have := mul_le_mul_of_nonneg_left hexp hprod.le
  rw [heq] at this
  linarith

theorem residual_positive_before_range (a b E X : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hE : 0 < E)
    (hX : X < stoppingRange a b E) : 0 < residualEnergy a b E X := by
  have harg : 0 < 1 + b / a * E := by positivity
  have hprod : 0 < E + a / b := by positivity
  have hexp : (1 + b / a * E)⁻¹ < Real.exp (-b * X) := by
    calc
      (1 + b / a * E)⁻¹ = Real.exp (-Real.log (1 + b / a * E)) := by
        rw [Real.exp_neg, Real.exp_log harg]
      _ < _ := by
        apply Real.exp_lt_exp.mpr
        dsimp [stoppingRange] at hX
        have h := (lt_div_iff₀ hb).mp hX
        nlinarith
  have heq : (E + a / b) * (1 + b / a * E)⁻¹ = a / b := by
    field_simp
    ring
  have hmul := mul_lt_mul_of_pos_left hexp hprod
  rw [heq] at hmul
  unfold residualEnergy
  exact lt_of_lt_of_le (sub_pos.mpr hmul) (le_max_right _ _)

theorem residual_zero_iff_range_reached (a b E X : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hE : 0 < E) :
    residualEnergy a b E X = 0 ↔ stoppingRange a b E ≤ X := by
  constructor
  · intro hz
    by_contra h
    have hp := residual_positive_before_range a b E X ha hb hE (lt_of_not_ge h)
    linarith
  · exact residual_zero_at_or_after_range a b E X ha hb hE

/-- The per-energy statement does not require a spectrum cutoff. -/
theorem stopped_before_detector_at_energy (a b E X : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hE : 0 < E) (hX : stoppingRange a b E < X) :
    ∃ Xstop, 0 < Xstop ∧ Xstop < X ∧ residualEnergy a b E Xstop = 0 ∧
      residualEnergy a b E X = 0 := by
  exact ⟨stoppingRange a b E, stopping_range_pos a b E ha hb hE, hX,
    residual_zero_at_or_after_range a b E _ ha hb hE le_rfl,
    residual_zero_at_or_after_range a b E X ha hb hE hX.le⟩

/-- A positive stopping depth strictly before the detector, including a population cutoff. -/
theorem stopped_before_detector (a b E Ecut X : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hE : 0 < E) (hcut : E ≤ Ecut)
    (hX : stoppingRange a b Ecut < X) :
    ∃ Xstop, 0 < Xstop ∧ Xstop < X ∧ residualEnergy a b E Xstop = 0 ∧
      residualEnergy a b E X = 0 := by
  have hbound := (range_mono a b E Ecut ha hb hE.le hcut).trans_lt hX
  exact ⟨stoppingRange a b E, stopping_range_pos a b E ha hb hE, hbound,
    residual_zero_at_or_after_range a b E _ ha hb hE le_rfl,
    residual_zero_at_or_after_range a b E X ha hb hE hbound.le⟩

def independentFPR (pA pB : ℝ) : ℝ := pA * pB

/-- Explicit joint factorization, conditional on background and the chosen window. -/
theorem factorized_joint_bounds (pA pB joint : ℝ)
    (hA : 0 < pA ∧ pA < 1) (hB : 0 < pB ∧ pB < 1)
    (hind : joint = pA * pB) : 0 < joint ∧ joint < min pA pB := by
  rw [hind]
  constructor
  · exact mul_pos hA.1 hB.1
  · apply lt_min
    · nlinarith [mul_pos hA.1 (sub_pos.mpr hB.2)]
    · nlinarith [mul_pos hB.1 (sub_pos.mpr hA.2)]

/-- A specified mixture: a common cause fires both; otherwise independent branches.
pA,pB are conditional marginals in the no-common-cause branch, not total marginals. -/
def commonCauseFPR (pC pA pB : ℝ) : ℝ := pC + (1 - pC) * independentFPR pA pB

theorem common_cause_zero (pA pB : ℝ) : commonCauseFPR 0 pA pB = independentFPR pA pB := by
  simp [commonCauseFPR]

theorem common_cause_floor (pC pA pB : ℝ) (hC : pC ≤ 1) (hA : 0 ≤ pA)
    (hB : 0 ≤ pB) : pC ≤ commonCauseFPR pC pA pB := by
  have := mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hA hB)
  dsimp [commonCauseFPR, independentFPR]
  linarith

/-- At least one success for IID Bernoulli windows; IID is the interpretation's premise. -/
def iidAnyFalseAlarm (p : ℝ) (windows : ℕ) : ℝ := 1 - (1 - p) ^ windows

theorem iid_any_positive (p : ℝ) (windows : ℕ) (hp : 0 < p ∧ p < 1)
    (hN : 0 < windows) : 0 < iidAnyFalseAlarm p windows := by
  have hpow : (1 - p) ^ windows < 1 :=
    pow_lt_one₀ (by linarith) (by linarith) (Nat.ne_of_gt hN)
  dsimp [iidAnyFalseAlarm]
  linarith

theorem explicit_single_window : independentFPR (1 / 100) (1 / 100) = 1 / 10000 ∧
    0 < independentFPR (1 / 100) (1 / 100) := by norm_num [independentFPR]

theorem explicit_many_windows : 0 < iidAnyFalseAlarm (1 / 10000) 10000 := by
  exact iid_any_positive _ _ (by norm_num) (by norm_num)

inductive TxState where
  | noSignal
  | signal (bit : Bool)
  deriving DecidableEq

abbrev RxSymbol := Option Bool

/-- Candidate bits are observations supplied by a decoder, not ground-truth TX labels. -/
def receive (trigger : Bool) (candidate : RxSymbol) : RxSymbol :=
  if trigger then candidate else none

theorem delivered_requires_trigger (trigger : Bool) (candidate : RxSymbol) (bit : Bool)
    (h : receive trigger candidate = some bit) : trigger = true := by
  cases trigger <;> simp_all [receive]

inductive Outcome where
  | correct | substitution | erasure | falseAlarm | rejectedBackground
  deriving DecidableEq

def classify : TxState → RxSymbol → Outcome
  | .noSignal, none => .rejectedBackground
  | .noSignal, some _ => .falseAlarm
  | .signal _, none => .erasure
  | .signal sent, some got => if sent = got then .correct else .substitution

/-- Ground truth is used only by evaluation. Every background trigger is a false
alarm, even if the decoder erases. Signal slots are scored after trigger gating. -/
def evaluate (tx : TxState) (trigger : Bool) (candidate : RxSymbol) : Outcome :=
  match tx with
  | .noSignal => if trigger then .falseAlarm else .rejectedBackground
  | .signal bit => classify (.signal bit) (receive trigger candidate)

theorem background_false_alarm_iff (trigger : Bool) (candidate : RxSymbol) :
    evaluate .noSignal trigger candidate = .falseAlarm ↔ trigger = true := by
  cases trigger <;> simp [evaluate]

theorem no_trigger_erases_signal (bit : Bool) (candidate : RxSymbol) :
    evaluate (.signal bit) false candidate = .erasure := rfl

/-- Probability masses of the five disjoint `evaluate` outcomes; normalization is explicit.
The model supplies these masses; no empirical estimates or traffic prior are inferred. -/
structure OutcomeMass where
  correct : ℝ
  flip : ℝ
  erased : ℝ
  falseAlarm : ℝ
  rejected : ℝ
  nonneg : 0 ≤ correct ∧ 0 ≤ flip ∧ 0 ≤ erased ∧ 0 ≤ falseAlarm ∧ 0 ≤ rejected
  normalized : correct + flip + erased + falseAlarm + rejected = 1

def signalMass (m : OutcomeMass) : ℝ := m.correct + m.flip + m.erased
def deliveredMass (m : OutcomeMass) : ℝ := m.correct + m.flip
def erasureRate (m : OutcomeMass) : ℝ := m.erased / signalMass m
def deliveredBER (m : OutcomeMass) : ℝ := m.flip / deliveredMass m
def falseAlarmRate (m : OutcomeMass) : ℝ := m.falseAlarm / (1 - signalMass m)
def totalFailureMass (m : OutcomeMass) : ℝ := m.erased + m.flip + m.falseAlarm

theorem background_mass (m : OutcomeMass) : 1 - signalMass m = m.falseAlarm + m.rejected := by
  dsimp [signalMass]
  linarith [m.normalized]

/-- Conditional error on signal slots: erasure plus delivered fraction times delivered BER. -/
theorem signal_error_decomposition (m : OutcomeMass)
    (hs : signalMass m ≠ 0) (hd : deliveredMass m ≠ 0) :
    (m.erased + m.flip) / signalMass m =
      erasureRate m + (1 - erasureRate m) * deliveredBER m := by
  unfold erasureRate deliveredBER
  have hsplit : signalMass m = deliveredMass m + m.erased := rfl
  field_simp
  rw [hsplit]
  ring

/-- Total error is prevalence-weighted; rates with different denominators cannot be added. -/
theorem total_error_decomposition (m : OutcomeMass)
    (hs : signalMass m ≠ 0) (hb : 1 - signalMass m ≠ 0) (hd : deliveredMass m ≠ 0) :
    totalFailureMass m =
      signalMass m * (erasureRate m + (1 - erasureRate m) * deliveredBER m) +
      (1 - signalMass m) * falseAlarmRate m := by
  rw [← signal_error_decomposition m hs hd]
  unfold falseAlarmRate totalFailureMass
  field_simp

structure PrometheusNoiseAuditSuite : Prop where
  stopping : ∀ a b E X, 0 < a → 0 < b → 0 < E → stoppingRange a b E ≤ X →
    residualEnergy a b E X = 0
  joint : ∀ (pA pB joint : ℝ), (0 < pA ∧ pA < 1) → (0 < pB ∧ pB < 1) →
    joint = pA * pB → 0 < joint ∧ joint < min pA pB
  counterexample : 0 < iidAnyFalseAlarm (1 / 10000) 10000
  receiver : ∀ trigger candidate bit, receive trigger candidate = some bit → trigger = true
  decomposition : ∀ m, signalMass m ≠ 0 → 1 - signalMass m ≠ 0 → deliveredMass m ≠ 0 →
    totalFailureMass m = signalMass m *
      (erasureRate m + (1 - erasureRate m) * deliveredBER m) +
      (1 - signalMass m) * falseAlarmRate m

theorem verification_suite : PrometheusNoiseAuditSuite :=
  ⟨residual_zero_at_or_after_range, factorized_joint_bounds, explicit_many_windows,
    delivered_requires_trigger, total_error_decomposition⟩
end
end PrometheusNoiseAudit

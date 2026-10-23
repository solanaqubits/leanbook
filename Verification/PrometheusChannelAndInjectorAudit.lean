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
# Conditional channel scalar and injector kinetic-energy audits

The entropy uses the real logarithm, with explicit analytic bounds. The scalar
d(1-H₂(p)) is the ideal memoryless erasure/substitution capacity expression.
A finite stipulated kernel, its mutual information and maximization over binary
input distributions are checked. An operational coding theorem and finite-code
reliability are not proved. An arbitrary finite code need not have rate below it.
Empirical frequencies are exact scenario inputs, not population estimates proved
by Lean. Latencies use rounded stipulated milliseconds, not the earlier sine
formula. Injector energy covers only the specified neutrons' kinetic energy,
not all reaction products, deposited energy, wall-plug input or engineering gain.
-/
namespace PrometheusChannelAndInjectorAudit
noncomputable section

/-- Binary entropy in bits; endpoint products use Lean's total real logarithm. -/
def binaryEntropy (p : ℝ) : ℝ :=
  (-p * Real.log p - (1 - p) * Real.log (1 - p)) / Real.log 2

def idealCapacity (erasure substitution : ℝ) : ℝ :=
  (1 - erasure) * (1 - binaryEntropy substitution)

inductive ChannelOutput where
  | erased | zero | one
  deriving DecidableEq

/-- A stipulated memoryless erasure/substitution transition row, not a detector model. -/
def transition (e p : ℝ) (sent : Bool) : ChannelOutput → ℝ
  | .erased => e
  | .zero => if sent then (1 - e) * p else (1 - e) * (1 - p)
  | .one => if sent then (1 - e) * (1 - p) else (1 - e) * p

def sumOutputs (f : ChannelOutput → ℝ) : ℝ := f .erased + f .zero + f .one

theorem transition_normalized (e p : ℝ) (sent : Bool) :
    sumOutputs (transition e p sent) = 1 := by
  cases sent <;> simp [sumOutputs, transition] <;> ring

theorem transition_nonnegative (e p : ℝ) (he : 0 ≤ e ∧ e ≤ 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (sent : Bool) (received : ChannelOutput) :
    0 ≤ transition e p sent received := by
  have he₀ := he.1
  have hp₀ := hp.1
  have he' : 0 ≤ 1 - e := sub_nonneg.mpr he.2
  have hp' : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  cases sent <;> cases received <;> simp only [transition, Bool.false_eq_true,
    ↓reduceIte] <;> positivity

/-- Output marginal for an explicitly uniform input bit. -/
def uniformOutputMass (e p : ℝ) (received : ChannelOutput) : ℝ :=
  (transition e p false received + transition e p true received) / 2

theorem uniform_output_erased (e p : ℝ) : uniformOutputMass e p .erased = e := by
  simp [uniformOutputMass, transition]

theorem uniform_output_zero (e p : ℝ) : uniformOutputMass e p .zero = (1 - e) / 2 := by
  simp [uniformOutputMass, transition]
  ring

theorem uniform_output_one (e p : ℝ) : uniformOutputMass e p .one = (1 - e) / 2 := by
  simp [uniformOutputMass, transition]
  ring

/-- Finite Shannon mutual-information sum: sum_x (1/2) sum_y W(y|x) log₂(W(y|x)/P(y)). -/
def uniformMutualInformation (e p : ℝ) : ℝ :=
  (sumOutputs (fun y => transition e p false y *
    Real.log (transition e p false y / uniformOutputMass e p y)) +
   sumOutputs (fun y => transition e p true y *
    Real.log (transition e p true y / uniformOutputMass e p y))) / (2 * Real.log 2)

/-- The scalar expression equals the uniform-input MI of the specified kernel.
This does not establish maximization over inputs or an operational coding theorem. -/
theorem uniform_information_formula (e p : ℝ) (he : 0 < e ∧ e < 1)
    (hp : 0 < p ∧ p < 1) : uniformMutualInformation e p = idealCapacity e p := by
  have hd : 1 - e ≠ 0 := ne_of_gt (sub_pos.mpr he.2)
  have hq : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  have hrp : (1 - e) * p / ((1 - e) / 2) = 2 * p := by
    field_simp
  have hrq : (1 - e) * (1 - p) / ((1 - e) / 2) = 2 * (1 - p) := by
    field_simp
  simp only [uniformMutualInformation, sumOutputs, uniform_output_erased,
    uniform_output_zero, uniform_output_one, transition, Bool.false_eq_true, ↓reduceIte]
  rw [div_self (ne_of_gt he.1), Real.log_one, hrp, hrq]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp.1),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hq]
  unfold idealCapacity binaryEntropy
  field_simp
  ring

def observedErasure : ℝ := 6664 / 10000
def observedSubstitution : ℝ := 34 / 3336
def observedDelivery : ℝ := 3336 / 10000
def observedCapacity : ℝ := idealCapacity observedErasure observedSubstitution

theorem input_domains :
    0 ≤ observedErasure ∧ observedErasure < 1 ∧
    0 < observedSubstitution ∧ observedSubstitution < 1 / 2 := by
  norm_num [observedErasure, observedSubstitution]

theorem delivery_fraction : 1 - observedErasure = observedDelivery := by
  norm_num [observedErasure, observedDelivery]

theorem delivery_above_third : 1 / 3 < observedDelivery := by norm_num [observedDelivery]

/-- A rational lower bound derived from log x ≥ 1 - 1/x, twice. -/
theorem log_two_lower : (7 : ℝ) / 12 ≤ Real.log 2 := by
  have h₁ := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
  have h₂ := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  have hm : Real.log 2 = Real.log (4 / 3) + Real.log (3 / 2) := by
    rw [← Real.log_mul (by norm_num : (4 : ℝ) / 3 ≠ 0) (by norm_num : (3 : ℝ) / 2 ≠ 0)]
    norm_num
  norm_num at h₁ h₂
  linarith

theorem log_two_positive : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The second entropy term is at most p, in natural-log units. -/
theorem complement_entropy_bound (p : ℝ) (hp : p < 1) :
    -(1 - p) * Real.log (1 - p) ≤ p := by
  have hq : 0 < 1 - p := by linarith
  have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hq) hq.le
  have heq : (1 - p) * (1 - (1 - p)⁻¹) = -p := by
    field_simp
    ring
  rw [heq] at h
  nlinarith

theorem observed_log_bound :
    -Real.log observedSubstitution < 7 * Real.log 2 := by
  have h := Real.log_lt_log
    (show (0 : ℝ) < observedSubstitution⁻¹ by norm_num [observedSubstitution])
    (show observedSubstitution⁻¹ < (2 : ℝ) ^ 7 by norm_num [observedSubstitution])
  simpa only [Real.log_inv, Real.log_pow, Nat.cast_ofNat] using h

/-- Exact analytic entropy bound; no floating-point evaluation of logarithms. -/
theorem observed_entropy_lt_nine_percent : binaryEntropy observedSubstitution < 9 / 100 := by
  apply (div_lt_iff₀ log_two_positive).2
  have hp : 0 < observedSubstitution := input_domains.2.2.1
  have hfirst := mul_lt_mul_of_pos_left observed_log_bound hp
  have hsecond := complement_entropy_bound observedSubstitution (by
    have := input_domains.2.2.2
    linarith)
  have htwo := log_two_lower
  dsimp [observedSubstitution] at hfirst hsecond ⊢
  nlinarith

theorem entropy_positive (p : ℝ) (hp : 0 < p) (hp1 : p < 1) : 0 < binaryEntropy p := by
  have hq : 0 < 1 - p := by linarith
  have hq1 : 1 - p < 1 := by linarith
  have hlp := Real.log_neg hp hp1
  have hlq := Real.log_neg hq hq1
  have hterm₁ := mul_pos hp (neg_pos.mpr hlp)
  have hterm₂ := mul_pos hq (neg_pos.mpr hlq)
  apply div_pos _ log_two_positive
  nlinarith

theorem observed_entropy_positive : 0 < binaryEntropy observedSubstitution := by
  exact entropy_positive _ input_domains.2.2.1 (by
    have := input_domains.2.2.2
    linarith)

theorem binary_entropy_half : binaryEntropy (1 / 2) = 1 := by
  have hl : Real.log (1 / 2) = -Real.log 2 := by
    simp
  norm_num [binaryEntropy]
  rw [hl]
  field_simp [ne_of_gt log_two_positive]
  ring

/-- Entropy's binary upper bound follows from log x ≤ x-1, not an oracle. -/
theorem binary_entropy_le_one (p : ℝ) (hp : 0 < p ∧ p < 1) : binaryEntropy p ≤ 1 := by
  have hp₀ := hp.1
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  have h₁ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (show 0 < (2 * p)⁻¹ by positivity)) hp.1.le
  have h₂ := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (show 0 < (2 * (1 - p))⁻¹ by positivity)) hq.le
  have heq₁ : p * ((2 * p)⁻¹ - 1) = 1 / 2 - p := by
    field_simp
  have heq₂ : (1 - p) * ((2 * (1 - p))⁻¹ - 1) = 1 / 2 - (1 - p) := by
    field_simp
  rw [heq₁, Real.log_inv, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp.1)] at h₁
  rw [heq₂, Real.log_inv, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hq)] at h₂
  apply (div_le_iff₀ log_two_positive).2
  nlinarith

/-- The bias is P(X=1); this is P(Y=1 | Y is not erased). -/
def outputBias (p bias : ℝ) : ℝ := (1 - bias) * p + bias * (1 - p)

private theorem positive_mixture (x y bias : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hb : 0 ≤ bias ∧ bias ≤ 1) : 0 < (1 - bias) * x + bias * y := by
  rcases eq_or_lt_of_le hb.2 with h | h
  · rw [h]
    simpa using hy
  · have h₁ := mul_pos (sub_pos.mpr h) hx
    have h₂ := mul_nonneg hb.1 hy.le
    linarith

theorem output_bias_domain (p bias : ℝ) (hp : 0 < p ∧ p < 1)
    (hb : 0 ≤ bias ∧ bias ≤ 1) : 0 < outputBias p bias ∧ outputBias p bias < 1 := by
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  have h₁ := positive_mixture p (1 - p) bias hp.1 hq hb
  have h₂ := positive_mixture (1 - p) p bias hq hp.1 hb
  dsimp [outputBias]
  constructor <;> nlinarith

def biasedOutputMass (e p bias : ℝ) (received : ChannelOutput) : ℝ :=
  (1 - bias) * transition e p false received + bias * transition e p true received

theorem biased_output_erased (e p bias : ℝ) : biasedOutputMass e p bias .erased = e := by
  simp [biasedOutputMass, transition]
  ring

theorem biased_output_zero (e p bias : ℝ) :
    biasedOutputMass e p bias .zero = (1 - e) * (1 - outputBias p bias) := by
  simp [biasedOutputMass, transition, outputBias]
  ring

theorem biased_output_one (e p bias : ℝ) :
    biasedOutputMass e p bias .one = (1 - e) * outputBias p bias := by
  simp [biasedOutputMass, transition, outputBias]
  ring

/-- Finite MI with arbitrary Bernoulli input; all probability weights are explicit. -/
def mutualInformation (e p bias : ℝ) : ℝ :=
  ((1 - bias) * sumOutputs (fun y => transition e p false y *
    Real.log (transition e p false y / biasedOutputMass e p bias y)) +
   bias * sumOutputs (fun y => transition e p true y *
    Real.log (transition e p true y / biasedOutputMass e p bias y))) / Real.log 2

theorem information_formula (e p bias : ℝ) (he : 0 < e ∧ e < 1)
    (hp : 0 < p ∧ p < 1) (hb : 0 ≤ bias ∧ bias ≤ 1) :
    mutualInformation e p bias = (1 - e) *
      (binaryEntropy (outputBias p bias) - binaryEntropy p) := by
  have hd : 1 - e ≠ 0 := ne_of_gt (sub_pos.mpr he.2)
  have hq : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp.2)
  have hr := output_bias_domain p bias hp hb
  have hr₁ : outputBias p bias ≠ 0 := ne_of_gt hr.1
  have hr₀ : 1 - outputBias p bias ≠ 0 := ne_of_gt (sub_pos.mpr hr.2)
  simp only [mutualInformation, sumOutputs, biased_output_erased,
    biased_output_zero, biased_output_one, transition, Bool.false_eq_true, ↓reduceIte,
    mul_div_mul_left _ _ hd, div_self (ne_of_gt he.1), Real.log_one]
  rw [Real.log_div hq hr₀, Real.log_div (ne_of_gt hp.1) hr₁,
    Real.log_div (ne_of_gt hp.1) hr₀, Real.log_div hq hr₁]
  dsimp [binaryEntropy, outputBias]
  field_simp
  ring

/-- Single-letter upper bound over every Bernoulli input, including deterministic inputs. -/
theorem information_le_capacity (e p bias : ℝ) (he : 0 < e ∧ e < 1)
    (hp : 0 < p ∧ p < 1) (hb : 0 ≤ bias ∧ bias ≤ 1) :
    mutualInformation e p bias ≤ idealCapacity e p := by
  rw [information_formula e p bias he hp hb]
  have h := binary_entropy_le_one _ (output_bias_domain p bias hp hb)
  have hd : 0 < 1 - e := sub_pos.mpr he.2
  dsimp [idealCapacity]
  nlinarith

theorem information_uniform_attains (e p : ℝ) (he : 0 < e ∧ e < 1)
    (hp : 0 < p ∧ p < 1) : mutualInformation e p (1 / 2) = idealCapacity e p := by
  rw [information_formula e p (1 / 2) he hp (by norm_num)]
  have hb : outputBias p (1 / 2) = 1 / 2 := by dsimp [outputBias]; ring
  rw [hb, binary_entropy_half]
  rfl

/-- A maximum over the whole binary-input simplex, not an operational rate converse. -/
theorem single_letter_capacity_maximum (e p : ℝ) (he : 0 < e ∧ e < 1)
    (hp : 0 < p ∧ p < 1) :
    (∀ bias, 0 ≤ bias → bias ≤ 1 → mutualInformation e p bias ≤ idealCapacity e p) ∧
    mutualInformation e p (1 / 2) = idealCapacity e p := by
  exact ⟨fun bias h₀ h₁ => information_le_capacity e p bias he hp ⟨h₀, h₁⟩,
    information_uniform_attains e p he hp⟩

theorem observed_capacity_lower : 3 / 10 < observedCapacity := by
  have hH := observed_entropy_lt_nine_percent
  dsimp [observedCapacity, idealCapacity, observedErasure]
  nlinarith

theorem observed_capacity_upper : observedCapacity < 1 := by
  have hH := observed_entropy_positive
  dsimp [observedCapacity, idealCapacity, observedErasure]
  nlinarith

def codeRate (informationBits channelUses : ℕ) : ℝ :=
  (informationBits : ℝ) / channelUses

/-- An arithmetic rate-budget certificate, not a code-existence/reliability theorem. -/
theorem conditional_rate_budget (k n : ℕ) (hn : 0 < n) (hbudget : 10 * k ≤ 3 * n) :
    codeRate k n < observedCapacity := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (10 : ℝ) * k ≤ 3 * n := by exact_mod_cast hbudget
  have hr : codeRate k n ≤ 3 / 10 := by
    apply (div_le_iff₀ hnR).2
    nlinarith
  exact hr.trans_lt observed_capacity_lower

/-- Only the algebraic rearrangement of an explicitly supplied Fano-style premise.
Deriving that premise from a finite probabilistic code remains a separate obligation. -/
theorem conditional_fano_rate_bound (k n : ℕ) (capacity error : ℝ)
    (hn : 0 < n) (he : error < 1)
    (hfano : (k : ℝ) ≤ n * capacity + 1 + error * k) :
    codeRate k n ≤ (capacity + 1 / n) / (1 - error) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heR : 0 < 1 - error := sub_pos.mpr he
  apply (le_div_iff₀ heR).2
  unfold codeRate
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).2
  field_simp
  nlinarith

/-- An injective finite encoder can operate above the scalar expression, with errors. -/
def identityEncoder (word : Fin 1 → Bool) : Fin 1 → Bool := word
def identityDecoder (word : Fin 1 → Bool) : Fin 1 → Bool := word

theorem identity_encoder_injective : Function.Injective identityEncoder := fun _ _ h => h

theorem identity_code_above_capacity : observedCapacity < codeRate 1 1 := by
  simpa [codeRate] using observed_capacity_upper

/-- A flipped observation is decoded incorrectly by this rate-one identity code. -/
theorem identity_code_flip_error :
    identityDecoder (fun _ => true) ≠ (fun _ : Fin 1 => false) := by
  intro h
  have := congrFun h 0
  simp [identityDecoder] at this

/-- Refutes a universal finite-code rate bound without a reliability requirement. -/
theorem not_every_finite_rate_below_capacity :
    ¬(∀ k n : ℕ, 0 < n → k ≤ n → codeRate k n ≤ observedCapacity) := by
  intro h
  have := h 1 1 (by norm_num) le_rfl
  linarith [identity_code_above_capacity]

/-- Milliseconds, using explicitly rounded propagation inputs. -/
def totalLatencyMs (channelUses : ℕ) (decodeMs : ℝ) : ℝ :=
  40410 / 1000 + (channelUses : ℝ) / 100000 + decodeMs

def roundedFiberMs : ℝ := 77921 / 1000

theorem latency_gap (n : ℕ) (decodeMs : ℝ) (hn : n ≤ 10000) (hdecode : decodeMs ≤ 1) :
    36411 / 1000 ≤ roundedFiberMs - totalLatencyMs n decodeMs := by
  have hnR : (n : ℝ) ≤ 10000 := by exact_mod_cast hn
  dsimp [roundedFiberMs, totalLatencyMs]
  linarith

theorem latency_below_fiber (n : ℕ) (decodeMs : ℝ) (hn : n ≤ 10000)
    (hdecode : decodeMs ≤ 1) : totalLatencyMs n decodeMs < roundedFiberMs := by
  have := latency_gap n decodeMs hn hdecode
  linarith

/-- Exact SI conversion. Other reaction products are not included. -/
def joulePerMeV : ℝ := 1602176634 / 10000000000000000000000
def injectorNeutronKineticJ : ℝ := 3000000 * (245 / 100) * joulePerMeV
def incidentLaserJ : ℝ := 16 / 10
def neutronKineticFraction : ℝ := injectorNeutronKineticJ / incidentLaserJ

theorem neutron_kinetic_exact : injectorNeutronKineticJ = 117759982599 / 100000000000000000 := by
  norm_num [injectorNeutronKineticJ, joulePerMeV]

theorem neutron_kinetic_bracket :
    11775 / 10000000000 < injectorNeutronKineticJ ∧
    injectorNeutronKineticJ < 11776 / 10000000000 := by
  norm_num [injectorNeutronKineticJ, joulePerMeV]

theorem neutron_fraction_bounds :
    0 < neutronKineticFraction ∧ neutronKineticFraction < 1 / 100000 ∧
      neutronKineticFraction < 1 := by
  norm_num [neutronKineticFraction, injectorNeutronKineticJ, joulePerMeV, incidentLaserJ]

structure PrometheusChannelAndInjectorAuditSuite : Prop where
  uniform_information : ∀ e p, (0 < e ∧ e < 1) → (0 < p ∧ p < 1) →
    uniformMutualInformation e p = idealCapacity e p
  single_letter : ∀ e p, (0 < e ∧ e < 1) → (0 < p ∧ p < 1) →
    (∀ bias, 0 ≤ bias → bias ≤ 1 → mutualInformation e p bias ≤ idealCapacity e p) ∧
    mutualInformation e p (1 / 2) = idealCapacity e p
  entropy : binaryEntropy observedSubstitution < 9 / 100
  capacity : 3 / 10 < observedCapacity
  finite_counterexample : observedCapacity < codeRate 1 1
  latency : ∀ n t, n ≤ 10000 → t ≤ 1 →
    36411 / 1000 ≤ roundedFiberMs - totalLatencyMs n t
  kinetic : injectorNeutronKineticJ = 117759982599 / 100000000000000000
  fraction : 0 < neutronKineticFraction ∧ neutronKineticFraction < 1 / 100000 ∧
    neutronKineticFraction < 1

theorem verification_suite : PrometheusChannelAndInjectorAuditSuite :=
  ⟨uniform_information_formula, single_letter_capacity_maximum,
    observed_entropy_lt_nine_percent, observed_capacity_lower, identity_code_above_capacity,
    latency_gap, neutron_kinetic_exact, neutron_fraction_bounds⟩
end
end PrometheusChannelAndInjectorAudit

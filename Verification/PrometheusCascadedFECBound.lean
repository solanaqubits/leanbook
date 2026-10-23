/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PrometheusFiniteBlockAudit

/-!
# Conditional IID cascade tail

Exact finite masses, five-vote ties erased, byte erasure on any erased bit.
The outer tail is not defined to be the implemented decoder's failure event.
No theorem here proves the GF256 Python implementation or a universal CRC bound.
-/
namespace PrometheusCascadedFECBound
noncomputable section
open scoped BigOperators
open PrometheusFiniteBlockAudit

@[simp] theorem ne_erased_correct : Noise.erased ≠ Noise.correct := by decide
@[simp] theorem ne_erased_flipped : Noise.erased ≠ Noise.flipped := by decide
@[simp] theorem ne_correct_erased : Noise.correct ≠ Noise.erased := by decide
@[simp] theorem ne_correct_flipped : Noise.correct ≠ Noise.flipped := by decide
@[simp] theorem ne_flipped_erased : Noise.flipped ≠ Noise.erased := by decide
@[simp] theorem ne_flipped_correct : Noise.flipped ≠ Noise.correct := by decide

/-- Order is erasure, correct, substitution. -/
def atom (e c t : ℚ) : Noise → ℚ
  | .erased => e
  | .correct => c
  | .flipped => t

def classify (score : ℤ) : Noise :=
  if score = 0 then .erased else if 0 < score then .flipped else .correct

theorem observed_tie_erased {r : ℕ} (sent : Bool) (noise : Fin r → Noise) :
    decode (fun i => observe sent (noise i)) = none ↔ noiseScore noise = 0 := by
  cases sent
  · rw [decode, observed_score_false]
    split_ifs <;> simp_all <;> omega
  · rw [decode, observed_score_true]
    split_ifs <;> simp_all <;> omega

def fiveMass (m : Noise → ℚ) (out : Noise) : ℚ :=
  ∑ a, ∑ b, ∑ c, ∑ d, ∑ e,
    m a * m b * m c * m d * m e * indicator
      (classify (noiseExponent a + noiseExponent b + noiseExponent c +
        noiseExponent d + noiseExponent e) = out)

def tiePolynomial (e c t : ℚ) : ℚ := e^5 + 20*e^3*c*t + 30*e*c^2*t^2

def errorPolynomial (e c t : ℚ) : ℚ :=
  5*e^4*t + 10*e^3*t^2 + 30*e^2*c*t^2 + 10*e^2*t^3 +
  20*e*c*t^3 + 10*c^2*t^3 + 5*e*t^4 + 5*c*t^4 + t^5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Expanding all 243 ternary vote patterns needs additional simplification heartbeats.
theorem five_mass_exact (e c t : ℚ) :
    fiveMass (atom e c t) .erased = tiePolynomial e c t ∧
    fiveMass (atom e c t) .flipped = errorPolynomial e c t ∧
    fiveMass (atom e c t) .correct = errorPolynomial e t c := by
  simp only [fiveMass, sum_noise]
  norm_num [atom, classify, noiseExponent, indicator, tiePolynomial, errorPolynomial]
  constructor
  · ring
  constructor <;> ring

theorem five_mass_nonnegative (m : Noise → ℚ) (hm : ∀ x, 0 ≤ m x) (out : Noise) :
    0 ≤ fiveMass m out := by
  apply Finset.sum_nonneg; intro a _
  apply Finset.sum_nonneg; intro b _
  apply Finset.sum_nonneg; intro c _
  apply Finset.sum_nonneg; intro d _
  apply Finset.sum_nonneg; intro e _
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hm a) (hm b))
    (hm c)) (hm d)) (hm e)) (indicator_nonnegative _)

theorem five_mass_normalized (e c t : ℚ) (h : e + c + t = 1) :
    ∑ out, fiveMass (atom e c t) out = 1 := by
  rw [sum_noise, (five_mass_exact e c t).1,
    (five_mass_exact e c t).2.2, (five_mass_exact e c t).2.1]
  calc
    _ = (e+c+t)^5 := by unfold tiePolynomial errorPolynomial; ring
    _ = 1 := by rw [h]; norm_num

/-- Probability all independent coordinates satisfy a predicate. -/
theorem all_mass (n : ℕ) (m : Noise → ℚ) (p : Noise → Prop) :
    (∑ w : Fin n → Noise, productMass m w * indicator (∀ i, p (w i))) =
      (∑ x, m x * indicator (p x))^n := by
  classical
  have hi (w : Fin n → Noise) : indicator (∀ i, p (w i)) =
      ∏ i, indicator (p (w i)) := by
    by_cases h : ∀ i, p (w i)
    · simp [indicator, h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [indicator, if_neg h]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [indicator, hi])
  simp_rw [hi]
  rw [product_expectation m (fun (_ : Fin n) x => indicator (p x))]
  simp

def byteClass (w : Fin 8 → Noise) : Noise :=
  if ∀ i, w i ≠ .erased then
    if ∀ i, w i = .correct then .correct else .flipped
  else .erased

def byteMass (m : Noise → ℚ) (out : Noise) : ℚ :=
  ∑ w : Fin 8 → Noise, productMass m w * indicator (byteClass w = out)

theorem byte_correct (m : Noise → ℚ) : byteMass m .correct = (m .correct)^8 := by
  classical
  have he (w : Fin 8 → Noise) : byteClass w = .correct ↔ ∀ i, w i = .correct := by
    unfold byteClass
    split_ifs with hn hc
    · exact ⟨fun _ => hc, fun _ => rfl⟩
    · simp [hc]
    · constructor
      · simp
      · intro hc; exact False.elim (hn (fun i => by rw [hc i]; decide))
  simp_rw [byteMass, he]
  rw [all_mass 8 m (fun x => x = .correct), sum_noise]
  simp [indicator]

theorem byte_erasure (m : Noise → ℚ) (hu : ∑ x, m x = 1) :
    byteMass m .erased = 1 - (m .correct + m .flipped)^8 := by
  classical
  have hi (w : Fin 8 → Noise) : indicator (byteClass w = .erased) =
      1 - indicator (∀ i, w i ≠ .erased) := by
    by_cases hn : ∀ i, w i ≠ .erased
    · simp [byteClass, hn, indicator]; split_ifs <;> simp
    · simp [byteClass, hn, indicator]
  simp_rw [byteMass, hi, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, product_mass_normalized m hu, 
    all_mass 8 m (fun x => x ≠ .erased), sum_noise]
  simp [indicator]

theorem byte_mass_normalized (m : Noise → ℚ) (hu : ∑ x, m x = 1) :
    ∑ out, byteMass m out = 1 := by
  classical
  unfold byteMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hi (w : Fin 8 → Noise) : ∑ out : Noise, indicator (byteClass w = out) = 1 := by
    rw [sum_noise]; cases byteClass w <;> norm_num [indicator]
  simp_rw [hi, mul_one]
  exact product_mass_normalized m hu

theorem byte_error (m : Noise → ℚ) (hu : ∑ x, m x = 1) :
    byteMass m .flipped = (m .correct + m .flipped)^8 - (m .correct)^8 := by
  have h := byte_mass_normalized m hu
  rw [sum_noise, byte_correct, byte_erasure m hu] at h
  linarith

def cost : Noise → ℕ | .correct => 0 | .erased => 1 | .flipped => 2

def weight {n : ℕ} (w : Fin n → Noise) : ℕ := ∑ i, cost (w i)

def errors {n : ℕ} (w : Fin n → Noise) : ℕ := ∑ i, if w i = .flipped then 1 else 0
def erasures {n : ℕ} (w : Fin n → Noise) : ℕ := ∑ i, if w i = .erased then 1 else 0

theorem weight_errors_erasures {n : ℕ} (w : Fin n → Noise) :
    weight w = 2 * errors w + erasures w := by
  have hc (x : Noise) : cost x = 2 * (if x = .flipped then 1 else 0) +
      (if x = .erased then 1 else 0) := by cases x <;> simp [cost]
  simp only [weight, errors, erasures, hc, Finset.sum_add_distrib, Finset.mul_sum]

def tail (n threshold : ℕ) (m : Noise → ℚ) : ℚ :=
  ∑ w : Fin n → Noise, productMass m w * indicator (threshold ≤ weight w)

theorem pgf (n : ℕ) (m : Noise → ℚ) (z : ℚ) :
    (∑ w : Fin n → Noise, productMass m w * z^(weight w)) =
      (m .correct + m .erased*z + m .flipped*z^2)^n := by
  have hp (w : Fin n → Noise) : z^(weight w) = ∏ i, z^(cost (w i)) := by
    exact (Finset.prod_pow_eq_pow_sum _ _ _).symm
  simp_rw [hp]
  rw [product_expectation m (fun (_ : Fin n) x => z^(cost x))]
  simp only [sum_noise, cost, pow_zero, pow_one, mul_one, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  congr 1
  ring

/-- Chernoff/Markov bound in rational PGF form, z = exp(theta) > 1.
This universal bound does not equate a tail with implemented packet failure. -/
theorem tail_bound (n threshold : ℕ) (m : Noise → ℚ) (hm : ∀ x, 0 ≤ m x)
    (z : ℚ) (hz : 1 < z) :
    tail n threshold m ≤ (m .correct + m .erased*z + m .flipped*z^2)^n / z^threshold := by
  have hz0 : 0 < z := lt_trans (by norm_num) hz
  have hi (w : Fin n → Noise) : indicator (threshold ≤ weight w) ≤ z^(weight w)/z^threshold := by
    by_cases h : threshold ≤ weight w
    · simp only [indicator, if_pos h]
      exact (one_le_div (pow_pos hz0 _)).2 (pow_le_pow_right₀ hz.le h)
    · simp only [indicator, if_neg h]
      exact div_nonneg (pow_nonneg hz0.le _) (pow_nonneg hz0.le _)
  calc
    tail n threshold m ≤ ∑ w : Fin n → Noise, productMass m w * (z^(weight w)/z^threshold) :=
      Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hi w)
        (product_mass_nonnegative m hm w)
    _ = (∑ w : Fin n → Noise, productMass m w * z^(weight w))/z^threshold := by
      simp_rw [← mul_div_assoc, div_eq_mul_inv]; rw [Finset.sum_mul]
    _ = _ := by rw [pgf]

def slotMass (pe ps : ℚ) : Noise → ℚ := atom pe ((1-pe)*(1-ps)) ((1-pe)*ps)

theorem slot_nonnegative (pe ps : ℚ) (he : 0 ≤ pe ∧ pe ≤ 1) (hs : 0 ≤ ps ∧ ps ≤ 1)
    (x : Noise) : 0 ≤ slotMass pe ps x := by
  cases x <;> simp only [slotMass, atom]
  · exact he.1
  · exact mul_nonneg (sub_nonneg.mpr he.2) (sub_nonneg.mpr hs.2)
  · exact mul_nonneg (sub_nonneg.mpr he.2) hs.1

theorem bit_normalized (pe ps : ℚ) : ∑ x, fiveMass (slotMass pe ps) x = 1 := by
  apply five_mass_normalized
  ring

theorem byte_nonnegative (m : Noise → ℚ) (hm : ∀ x, 0 ≤ m x) (out : Noise) :
    0 ≤ byteMass m out := by
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg (product_mass_nonnegative m hm w) (indicator_nonnegative _)

def cascadeLaw (pe ps : ℚ) : Noise → ℚ := byteMass (fiveMass (slotMass pe ps))

theorem cascade_normalized (pe ps : ℚ) : ∑ x, cascadeLaw pe ps x = 1 :=
  byte_mass_normalized _ (bit_normalized pe ps)

def cascadeMoment (pe ps z : ℚ) : ℚ :=
  let e := tiePolynomial pe ((1-pe)*(1-ps)) ((1-pe)*ps)
  let c := errorPolynomial pe ((1-pe)*ps) ((1-pe)*(1-ps))
  c^8 + (1-(1-e)^8)*z + ((1-e)^8-c^8)*z^2

theorem cascade_moment_exact (pe ps z : ℚ) :
    cascadeLaw pe ps .correct + cascadeLaw pe ps .erased*z +
      cascadeLaw pe ps .flipped*z^2 = cascadeMoment pe ps z := by
  have hn := bit_normalized pe ps
  have hc := (five_mass_exact pe ((1-pe)*(1-ps)) ((1-pe)*ps)).2.2
  have he := (five_mass_exact pe ((1-pe)*(1-ps)) ((1-pe)*ps)).1
  change fiveMass (slotMass pe ps) .correct = _ at hc
  change fiveMass (slotMass pe ps) .erased = _ at he
  have hs : fiveMass (slotMass pe ps) .correct + fiveMass (slotMass pe ps) .flipped =
      1 - fiveMass (slotMass pe ps) .erased := by rw [sum_noise] at hn; linarith
  unfold cascadeLaw
  rw [byte_correct, byte_erasure _ hn, byte_error _ hn, hs, hc, he]
  rfl

theorem cascade_bound (pe ps z : ℚ) (he : 0 ≤ pe ∧ pe ≤ 1) (hs : 0 ≤ ps ∧ ps ≤ 1)
    (hz : 1 < z) : tail 240 205 (cascadeLaw pe ps) ≤ (cascadeMoment pe ps z)^240/z^205 := by
  have hm := byte_nonnegative _ (five_mass_nonnegative _ (slot_nonnegative pe ps he hs))
  have h := tail_bound 240 205 (cascadeLaw pe ps) hm z hz
  rwa [cascade_moment_exact] at h

/-- Exact coarse arithmetic certificate, conditional IID tail only. -/
theorem rounded_iid_certificate :
    tail 240 205 (cascadeLaw (6664/10000) (10192/1000000)) < 12/1000000 := by
  have h := cascade_bound (6664/10000) (10192/1000000) 2 (by norm_num) (by norm_num) (by norm_num)
  have hm : 0 ≤ cascadeMoment (6664/10000) (10192/1000000) 2 ∧
      cascadeMoment (6664/10000) (10192/1000000) 2 ≤ 1724191/1000000 := by
    norm_num [cascadeMoment, tiePolynomial, errorPolynomial]
  apply lt_of_le_of_lt h
  calc
    _ ≤ (1724191/1000000 : ℚ)^240/2^205 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hm.1 hm.2 240) (by norm_num)
    _ < 12/1000000 := by norm_num

/-- Separate historical rational input; no silent replacement by its rounded value. -/
theorem historical_iid_certificate :
    tail 240 205 (cascadeLaw (6664/10000) (34/3336)) < 12/1000000 := by
  have h := cascade_bound (6664/10000) (34/3336) 2 (by norm_num) (by norm_num) (by norm_num)
  have hm : 0 ≤ cascadeMoment (6664/10000) (34/3336) 2 ∧
      cascadeMoment (6664/10000) (34/3336) 2 ≤ 1724191/1000000 := by
    norm_num [cascadeMoment, tiePolynomial, errorPolynomial]
  apply lt_of_le_of_lt h
  calc
    _ ≤ (1724191/1000000 : ℚ)^240/2^205 :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hm.1 hm.2 240) (by norm_num)
    _ < 12/1000000 := by norm_num

/-- A correctness bridge is an explicit premise, not a verified Python decoder. -/
theorem failure_bound (n : ℕ) (m : Noise → ℚ) (hm : ∀ x, 0 ≤ m x)
    (failure : (Fin n → Noise) → Prop)
    (correct_within : ∀ w, weight w ≤ 204 → ¬ failure w) (z : ℚ) (hz : 1 < z) :
    (∑ w, productMass m w * indicator (failure w)) ≤
      (m .correct + m .erased*z + m .flipped*z^2)^n/z^205 := by
  classical
  apply le_trans _ (tail_bound n 205 m hm z hz)
  apply Finset.sum_le_sum
  intro w _
  apply mul_le_mul_of_nonneg_left _ (product_mass_nonnegative m hm w)
  by_cases hf : failure w
  · have hw : 205 ≤ weight w := by
      by_contra h; exact correct_within w (by omega) hf
    simp [indicator, hf, hw]
  · simp only [indicator, if_neg hf]; split_ifs <;> norm_num

/-- Correct framing is not an authentication property: every payload has a valid tag. -/
def tagged {Payload Tag : Type*} (crc : Payload → Tag) (p : Payload) : Payload × Tag := (p, crc p)
def crcAccept {Payload Tag : Type*} (crc : Payload → Tag) (frame : Payload × Tag) : Prop :=
  frame.2 = crc frame.1

theorem wrong_valid_frame {Payload Tag : Type*} (crc : Payload → Tag) (p q : Payload)
    (hne : p ≠ q) : crcAccept crc (tagged crc q) ∧ tagged crc q ≠ tagged crc p := by
  constructor
  · rfl
  · intro h; exact hne (congrArg Prod.fst h).symm

theorem packet_dimensions : 256+32=36*8 ∧ 240*8*5=9600 ∧ 240-36+1=205 := by norm_num

structure PrometheusCascadedFECBoundSuite : Prop where
  chernoff : ∀ n threshold m, (∀ x, 0 ≤ m x) → ∀ z, 1 < z →
    tail n threshold m ≤ (m .correct + m .erased*z + m .flipped*z^2)^n/z^threshold
  byte_error_formula : ∀ m, (∑ x, m x=1) →
    byteMass m .flipped = (m .correct+m .flipped)^8-(m .correct)^8

theorem verification_suite : PrometheusCascadedFECBoundSuite := ⟨tail_bound, byte_error⟩
end
end PrometheusCascadedFECBound

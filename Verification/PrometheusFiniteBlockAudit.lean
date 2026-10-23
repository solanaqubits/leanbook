/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Constructive finite-block bound for an explicitly IID erasure/substitution channel

The code repeats each payload bit 100 times. A blind majority decoder returns an
erasure on ties. All probabilities are actual finite sums under normalized product
distributions, with exact rational parameters. A product likelihood bound and a
finite union bound establish maximum (every-message) packet failure probability.
This is not a normal approximation, optimal-rate claim, PPV theorem, hardware
channel validation, or certificate for the separate fixed-256-bit benchmark.
-/
namespace PrometheusFiniteBlockAudit
noncomputable section
open scoped BigOperators

inductive Noise where
  | erased | correct | flipped
  deriving DecidableEq

instance : Fintype Noise := ⟨{.erased, .correct, .flipped}, by
  intro z
  cases z <;> simp⟩

def erasureProbability : ℚ := 6664 / 10000
def substitutionProbability : ℚ := 10192 / 1000000

def noiseMass : Noise → ℚ
  | .erased => erasureProbability
  | .correct => (1 - erasureProbability) * (1 - substitutionProbability)
  | .flipped => (1 - erasureProbability) * substitutionProbability

theorem sum_noise (f : Noise → ℚ) :
    ∑ z, f z = f .erased + f .correct + f .flipped := by
  have hu : (Finset.univ : Finset Noise) = {.erased, .correct, .flipped} := by decide
  rw [hu]
  simp
  ring

theorem noise_mass_nonnegative (z : Noise) : 0 ≤ noiseMass z := by
  cases z <;> norm_num [noiseMass, erasureProbability, substitutionProbability]

theorem noise_mass_normalized : ∑ z, noiseMass z = 1 := by
  rw [sum_noise]
  norm_num [noiseMass, erasureProbability, substitutionProbability]

/-- Independent product mass; independence is encoded by multiplication. -/
def productMass {ι Ω : Type*} [Fintype ι] (mass : Ω → ℚ) (word : ι → Ω) : ℚ :=
  ∏ i, mass (word i)

theorem product_mass_nonnegative {ι Ω : Type*} [Fintype ι]
    (mass : Ω → ℚ) (hm : ∀ x, 0 ≤ mass x) (word : ι → Ω) :
    0 ≤ productMass mass word := Finset.prod_nonneg fun i _ => hm (word i)

theorem product_mass_normalized {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (mass : Ω → ℚ) (hm : ∑ x, mass x = 1) :
    ∑ word : ι → Ω, productMass mass word = 1 := by
  classical
  simp only [productMass]
  rw [← Fintype.prod_sum]
  simp [hm]

theorem product_expectation {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (mass : Ω → ℚ) (f : ι → Ω → ℚ) :
    ∑ word : ι → Ω, productMass mass word * (∏ i, f i (word i)) =
      ∏ i, ∑ x, mass x * f i x := by
  classical
  simp only [productMass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun i x => mass x * f i x).symm

theorem product_marginal {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (mass : Ω → ℚ) (hm : ∑ x, mass x = 1) (i : ι) (f : Ω → ℚ) :
    ∑ word : ι → Ω, productMass mass word * f (word i) = ∑ x, mass x * f x := by
  classical
  have h := product_expectation mass (fun j x => if j = i then f x else 1)
  have hs (j : ι) : (∑ x, mass x * (if j = i then f x else 1)) =
      if j = i then ∑ x, mass x * f x else 1 := by
    by_cases hj : j = i <;> simp [hj, hm]
  simp_rw [hs] at h
  simpa using h

def indicator (P : Prop) : ℚ := by classical exact if P then 1 else 0

theorem indicator_nonnegative (P : Prop) : 0 ≤ indicator P := by
  classical
  by_cases h : P <;> simp [indicator, h]

theorem indicator_le_one (P : Prop) : indicator P ≤ 1 := by
  classical
  by_cases h : P <;> simp [indicator, h]

theorem finite_probability_bounds {Ω : Type*} [Fintype Ω]
    (mass : Ω → ℚ) (hm : ∀ x, 0 ≤ mass x) (hunit : ∑ x, mass x = 1)
    (event : Ω → Prop) :
    0 ≤ (∑ x, mass x * indicator (event x)) ∧
      (∑ x, mass x * indicator (event x)) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hm x) (indicator_nonnegative (event x))
  · calc
      (∑ x, mass x * indicator (event x)) ≤ ∑ x, mass x * 1 :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (indicator_le_one (event x)) (hm x)
      _ = 1 := by simpa using hunit

theorem indicator_union_le {ι : Type*} [Fintype ι] (P : ι → Prop) :
    indicator (∃ i, P i) ≤ ∑ i, indicator (P i) := by
  classical
  by_cases h : ∃ i, P i
  · obtain ⟨i, hi⟩ := h
    have hexists : ∃ i, P i := ⟨i, hi⟩
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      indicator_nonnegative (P j)) (Finset.mem_univ i)
    simpa only [indicator, if_pos hi, if_pos hexists] using hs
  · simp only [indicator, if_neg h]
    exact Finset.sum_nonneg fun i _ => indicator_nonnegative (P i)

/-- Channel emission, distinct from decoder. The decoder never sees Noise labels. -/
def observe (sent : Bool) : Noise → Option Bool
  | .erased => none
  | .correct => some sent
  | .flipped => some (!sent)

def vote : Option Bool → ℤ
  | none => 0
  | some false => -1
  | some true => 1

def receivedScore {r : ℕ} (received : Fin r → Option Bool) : ℤ := ∑ i, vote (received i)

/-- Positive/negative majority; a tie, including all erasures, returns none. -/
def decode {r : ℕ} (received : Fin r → Option Bool) : Option Bool :=
  if 0 < receivedScore received then some true
  else if receivedScore received < 0 then some false else none

/-- Exponent is flipped-minus-correct, not an input available to the decoder. -/
def noiseExponent : Noise → ℤ
  | .erased => 0
  | .correct => -1
  | .flipped => 1

def noiseScore {r : ℕ} (noise : Fin r → Noise) : ℤ := ∑ i, noiseExponent (noise i)

theorem observed_score_false {r : ℕ} (noise : Fin r → Noise) :
    receivedScore (fun i => observe false (noise i)) = noiseScore noise := by
  apply Finset.sum_congr rfl
  intro i _
  cases h : noise i <;> simp [observe, vote, noiseExponent, h]

theorem observed_score_true {r : ℕ} (noise : Fin r → Noise) :
    receivedScore (fun i => observe true (noise i)) = -noiseScore noise := by
  unfold receivedScore noiseScore
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases h : noise i <;> simp [observe, vote, noiseExponent, h]

theorem decode_failure_iff {r : ℕ} (sent : Bool) (noise : Fin r → Noise) :
    decode (fun i => observe sent (noise i)) ≠ some sent ↔ 0 ≤ noiseScore noise := by
  cases sent
  · rw [decode, observed_score_false]
    split_ifs <;> simp_all
    omega
  · rw [decode, observed_score_true]
    split_ifs <;> simp_all

def likelihoodFactor (z : Noise) : ℚ := 10 ^ noiseExponent z
def likelihoodWeight {r : ℕ} (noise : Fin r → Noise) : ℚ := ∏ i, likelihoodFactor (noise i)
def oneUseMoment : ℚ := ∑ z, noiseMass z * likelihoodFactor z

theorem product_zpow_eq_sum {ι : Type*} [Fintype ι] (exponent : ι → ℤ) :
    (∏ i, (10 : ℚ) ^ exponent i) = 10 ^ (∑ i, exponent i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
      zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]

theorem likelihood_weight_eq {r : ℕ} (noise : Fin r → Noise) :
    likelihoodWeight noise = (10 : ℚ) ^ noiseScore noise := product_zpow_eq_sum _

theorem indicator_failure_le_weight {r : ℕ} (sent : Bool) (noise : Fin r → Noise) :
    indicator (decode (fun i => observe sent (noise i)) ≠ some sent) ≤ likelihoodWeight noise := by
  rw [decode_failure_iff, likelihood_weight_eq]
  by_cases h : 0 ≤ noiseScore noise
  · simp only [indicator, if_pos h]
    exact one_le_zpow₀ (by norm_num : (1 : ℚ) ≤ 10) h
  · simp only [indicator, if_neg h]
    exact zpow_nonneg (by norm_num) _

theorem moment_exact : oneUseMoment = 572984771 / 781250000 := by
  rw [oneUseMoment, sum_noise]
  norm_num [noiseMass, likelihoodFactor, noiseExponent, erasureProbability, substitutionProbability]

theorem moment_bounds : 0 ≤ oneUseMoment ∧ oneUseMoment < 3 / 4 := by
  rw [moment_exact]
  norm_num

/-- Actual failure probability, not a bound introduced as a definition. -/
def bitFailureProbability (r : ℕ) (sent : Bool) : ℚ :=
  ∑ noise : Fin r → Noise, productMass noiseMass noise *
    indicator (decode (fun i => observe sent (noise i)) ≠ some sent)

theorem bit_probability_bounds (r : ℕ) (sent : Bool) :
    0 ≤ bitFailureProbability r sent ∧ bitFailureProbability r sent ≤ 1 :=
  finite_probability_bounds _ (product_mass_nonnegative noiseMass noise_mass_nonnegative)
    (product_mass_normalized noiseMass noise_mass_normalized) _

theorem likelihood_expectation (r : ℕ) :
    ∑ noise : Fin r → Noise, productMass noiseMass noise * likelihoodWeight noise =
      oneUseMoment ^ r := by
  unfold likelihoodWeight
  rw [product_expectation]
  simp [oneUseMoment]

theorem bit_failure_bound (r : ℕ) (sent : Bool) :
    bitFailureProbability r sent ≤ (3 / 4 : ℚ) ^ r := by
  calc
    bitFailureProbability r sent ≤
        ∑ noise, productMass noiseMass noise * likelihoodWeight noise := by
      apply Finset.sum_le_sum
      intro noise _
      exact mul_le_mul_of_nonneg_left (indicator_failure_le_weight sent noise)
        (product_mass_nonnegative noiseMass noise_mass_nonnegative noise)
    _ = oneUseMoment ^ r := likelihood_expectation r
    _ ≤ (3 / 4 : ℚ) ^ r := pow_le_pow_left₀ moment_bounds.1 moment_bounds.2.le r

def repeatEncode {k : ℕ} (r : ℕ) (message : Fin k → Bool) : Fin k → Fin r → Bool :=
  fun i _ => message i

theorem repeat_encoder_injective (k r : ℕ) (hr : 0 < r) :
    Function.Injective (repeatEncode (k := k) r) := by
  intro a b h
  funext i
  exact congrFun (congrFun h i) ⟨0, hr⟩

def packetDecode {k r : ℕ} (received : Fin k → Fin r → Option Bool) : Fin k → Option Bool :=
  fun i => decode (received i)

def packetFailureProbability {k : ℕ} (r : ℕ) (message : Fin k → Bool) : ℚ :=
  ∑ noise : Fin k → Fin r → Noise, productMass (productMass noiseMass) noise *
    indicator (∃ i, packetDecode (fun j t => observe (message j) (noise j t)) i ≠ some (message i))

theorem repeated_channel_observations {k r : ℕ} (message : Fin k → Bool)
    (noise : Fin k → Fin r → Noise) :
    (fun i t => observe (repeatEncode r message i t) (noise i t)) =
      (fun i t => observe (message i) (noise i t)) := rfl

theorem packet_failure_iff_decoder_mismatch {k r : ℕ} (message : Fin k → Bool)
    (noise : Fin k → Fin r → Noise) :
    (∃ i, packetDecode (fun j t => observe (message j) (noise j t)) i ≠ some (message i)) ↔
    packetDecode (fun j t => observe (message j) (noise j t)) ≠ (fun i => some (message i)) := by
  classical
  simp only [ne_eq, funext_iff, not_forall]

theorem packet_mass_normalized (k r : ℕ) :
    ∑ noise : Fin k → Fin r → Noise, productMass (productMass noiseMass) noise = 1 := by
  exact product_mass_normalized _
    (product_mass_normalized (ι := Fin r) noiseMass noise_mass_normalized)

theorem packet_probability_bounds {k : ℕ} (r : ℕ) (message : Fin k → Bool) :
    0 ≤ packetFailureProbability r message ∧ packetFailureProbability r message ≤ 1 :=
  finite_probability_bounds _
    (product_mass_nonnegative _ (product_mass_nonnegative noiseMass noise_mass_nonnegative))
    (packet_mass_normalized k r) _

/-- Union bound derived for every message; no uniform-message averaging assumption. -/
theorem packet_failure_bound {k : ℕ} (r : ℕ) (message : Fin k → Bool) :
    packetFailureProbability r message ≤ (k : ℚ) * (3 / 4 : ℚ) ^ r := by
  classical
  calc
    packetFailureProbability r message ≤
        ∑ noise : Fin k → Fin r → Noise, productMass (productMass noiseMass) noise *
          (∑ i, indicator
            (decode (fun t => observe (message i) (noise i t)) ≠ some (message i))) := by
      apply Finset.sum_le_sum
      intro noise _
      exact mul_le_mul_of_nonneg_left (indicator_union_le _)
        (product_mass_nonnegative _
          (product_mass_nonnegative noiseMass noise_mass_nonnegative) noise)
    _ = ∑ i : Fin k, bitFailureProbability r (message i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact product_marginal _
        (product_mass_normalized (ι := Fin r) noiseMass noise_mass_normalized) i
        (fun block => indicator
          (decode (fun t => observe (message i) (block t)) ≠ some (message i)))
    _ ≤ ∑ _i : Fin k, (3 / 4 : ℚ) ^ r := by
      exact Finset.sum_le_sum fun i _ => bit_failure_bound r (message i)
    _ = _ := by simp

theorem two_hundred_certificate : (200 : ℚ) * (3 / 4 : ℚ) ^ 100 < 1 / 1000000000 := by
  norm_num

/-- All payloads up to 200 bits have a strict finite-block PER certificate at 100 repeats. -/
theorem repeated_packet_per_lt {k : ℕ} (hk : k ≤ 200) (message : Fin k → Bool) :
    packetFailureProbability 100 message < 1 / 1000000000 := by
  have hkQ : (k : ℚ) ≤ 200 := by exact_mod_cast hk
  have hpow : 0 ≤ (3 / 4 : ℚ) ^ 100 := by positivity
  exact (packet_failure_bound 100 message).trans_lt
    ((mul_le_mul_of_nonneg_right hkQ hpow).trans_lt two_hundred_certificate)

def channelUses (k r : ℕ) : ℕ := k * r

theorem encoder_positions (k r : ℕ) : Fintype.card (Fin k × Fin r) = channelUses k r := by
  simp [channelUses]

theorem four_block_lengths : channelUses 10 100 = 1000 ∧ channelUses 50 100 = 5000 ∧
    channelUses 100 100 = 10000 ∧ channelUses 200 100 = 20000 := by norm_num [channelUses]

theorem repetition_rate (k : ℕ) (hk : 0 < k) :
    (k : ℚ) / channelUses k 100 = 1 / 100 := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  simp only [channelUses, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

/-- A larger bound failing the target is not a lower bound on actual failure. -/
theorem fixed_256_loose_certificate :
    (1 : ℚ) / 1000000000 < 256 * (3 / 4 : ℚ) ^ 78 := by norm_num

/-- A contrasting channel: one common draw is reused across all 100 positions. -/
def sharedDrawFailureProbability (sent : Bool) : ℚ :=
  ∑ z, noiseMass z * indicator (decode (fun _ : Fin 100 => observe sent z) ≠ some sent)

theorem shared_draw_single_position_marginal (i : Fin 100) (z : Noise) :
    (∑ draw, noiseMass draw * indicator ((fun _ : Fin 100 => draw) i = z)) = noiseMass z := by
  simp [indicator]

/-- Same one-position marginals do not imply the independent repetition guarantee. -/
theorem shared_draw_failure_exact (sent : Bool) :
    sharedDrawFailureProbability sent = 52328129 / 78125000 := by
  rw [sharedDrawFailureProbability, sum_noise]
  cases sent <;> norm_num [noiseMass, indicator, decode, receivedScore, observe, vote,
    erasureProbability, substitutionProbability] <;> simp only [reduceCtorEq, ↓reduceIte] <;>
    norm_num

theorem shared_draw_failure_large (sent : Bool) :
    1 / 2 < sharedDrawFailureProbability sent := by rw [shared_draw_failure_exact]; norm_num

structure PrometheusFiniteBlockAuditSuite : Prop where
  normalized : ∀ k r, (∑ noise : Fin k → Fin r → Noise,
    productMass (productMass noiseMass) noise) = 1
  decoder : ∀ r sent (noise : Fin r → Noise),
    decode (fun i => observe sent (noise i)) ≠ some sent ↔ 0 ≤ noiseScore noise
  finite_bound : ∀ k r (message : Fin k → Bool),
    packetFailureProbability r message ≤ (k : ℚ) * (3 / 4 : ℚ) ^ r
  certified : ∀ k, k ≤ 200 → ∀ message : Fin k → Bool,
    packetFailureProbability 100 message < 1 / 1000000000

theorem verification_suite : PrometheusFiniteBlockAuditSuite :=
  ⟨packet_mass_normalized, fun _ => decode_failure_iff,
    fun _ => packet_failure_bound, fun _ => repeated_packet_per_lt⟩
end
end PrometheusFiniteBlockAudit

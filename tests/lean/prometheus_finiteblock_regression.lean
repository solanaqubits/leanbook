import Verification.PrometheusFiniteBlockAudit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

open PrometheusFiniteBlockAudit
open scoped BigOperators

-- Independent exact arithmetic: these are stipulated decimals, not measured probabilities.
example : erasureProbability = 833 / 1250 := by norm_num [erasureProbability]
example : substitutionProbability = 637 / 62500 := by norm_num [substitutionProbability]
example : substitutionProbability ≠ 34 / 3336 := by norm_num [substitutionProbability]
example : noiseMass .flipped = 265629 / 78125000 := by
  norm_num [noiseMass, erasureProbability, substitutionProbability]
example : noiseMass .correct = 25796871 / 78125000 := by
  norm_num [noiseMass, erasureProbability, substitutionProbability]
example : (∑ z, noiseMass z) = 1 := noise_mass_normalized
example : oneUseMoment = 73342050688 / 100000000000 := by rw [moment_exact]; norm_num
example : oneUseMoment < 3 / 4 := moment_bounds.2
example : 0 < oneUseMoment := by rw [moment_exact]; norm_num

-- The receiver has observations only, with no access to transmitted labels.
example : observe false .correct = some false := rfl
example : observe true .flipped = some false := rfl
example : observe true .erased = none := rfl
example : decode (fun _ : Fin 0 => some true) = none := by
  simp [decode, receivedScore]
example : decode (fun _ : Fin 1 => some true) = some true := by
  norm_num [decode, receivedScore, vote]
example : decode (fun _ : Fin 1 => some false) = some false := by
  norm_num [decode, receivedScore, vote]
example : decode (fun _ : Fin 100 => none) = none := by
  simp [decode, receivedScore, vote]
example : decode (![some false, some true]) = none := by
  norm_num [decode, receivedScore, vote, Fin.sum_univ_two]
example : decode (![none, some true, some false]) = none := by
  norm_num [decode, receivedScore, vote, Fin.sum_univ_succ]
example : decode (![none, some true, some true]) = some true := by
  norm_num [decode, receivedScore, vote, Fin.sum_univ_succ]
example (sent : Bool) (noise : Fin 7 → Noise) :
    decode (fun i => observe sent (noise i)) ≠ some sent ↔ 0 ≤ noiseScore noise :=
  decode_failure_iff sent noise

-- Actual finite distributions, probability bounds and encoder injection.
example (r : ℕ) : (∑ noise : Fin r → Noise, productMass noiseMass noise) = 1 :=
  product_mass_normalized noiseMass noise_mass_normalized
example (k r : ℕ) : (∑ noise : Fin k → Fin r → Noise,
    productMass (productMass noiseMass) noise) = 1 := packet_mass_normalized k r
example (sent : Bool) : 0 ≤ bitFailureProbability 100 sent ∧
    bitFailureProbability 100 sent ≤ 1 := bit_probability_bounds 100 sent
example (message : Fin 200 → Bool) : 0 ≤ packetFailureProbability 100 message ∧
    packetFailureProbability 100 message ≤ 1 := packet_probability_bounds 100 message
example : Function.Injective (repeatEncode (k := 200) 100) :=
  repeat_encoder_injective 200 100 (by norm_num)
example : Fintype.card (Fin 200 × Fin 100) = channelUses 200 100 := encoder_positions 200 100
example (message : Fin 7 → Bool) : repeatEncode 100 message = fun i _ => message i := rfl
example (sent : Bool) : bitFailureProbability 100 sent ≤ (3 / 4 : ℚ) ^ 100 :=
  bit_failure_bound 100 sent
example (message : Fin 200 → Bool) :
    packetFailureProbability 100 message ≤ 200 * (3 / 4 : ℚ) ^ 100 :=
  packet_failure_bound 100 message

-- Boundary witnesses: no observations lose a bit; an empty payload cannot fail.
example (sent : Bool) : bitFailureProbability 0 sent = 1 := by
  simp [bitFailureProbability, productMass, indicator, decode, receivedScore]
example (r : ℕ) (message : Fin 0 → Bool) : packetFailureProbability r message = 0 := by
  simp [packetFailureProbability, indicator]
example : 256 * 78 ≤ 20000 ∧ 20000 < 256 * 79 := by norm_num

-- Nonasymptotic maximum error: every message at each specified block length.
example (m : Fin 10 → Bool) : packetFailureProbability 100 m < 1 / 1000000000 :=
  repeated_packet_per_lt (by norm_num) m
example (m : Fin 50 → Bool) : packetFailureProbability 100 m < 1 / 1000000000 :=
  repeated_packet_per_lt (by norm_num) m
example (m : Fin 100 → Bool) : packetFailureProbability 100 m < 1 / 1000000000 :=
  repeated_packet_per_lt (by norm_num) m
example (m : Fin 200 → Bool) : packetFailureProbability 100 m < 1 / 1000000000 :=
  repeated_packet_per_lt (by norm_num) m
example : channelUses 10 100 = 1000 ∧ channelUses 50 100 = 5000 ∧
    channelUses 100 100 = 10000 ∧ channelUses 200 100 = 20000 := four_block_lengths
example : (200 : ℚ) / channelUses 200 100 = 1 / 100 := repetition_rate 200 (by norm_num)
example : (200 : ℚ) * (3 / 4) ^ 100 < 65 / 1000000000000 := by norm_num
example : (1 : ℚ) / 1000000000 < 256 * (3 / 4) ^ 78 := fixed_256_loose_certificate

-- Correlation counterexample has identical marginals but failure above one half.
example (i : Fin 100) (z : Noise) :
    (∑ draw, noiseMass draw * indicator ((fun _ : Fin 100 => draw) i = z)) = noiseMass z :=
  shared_draw_single_position_marginal i z
example : sharedDrawFailureProbability false = 52328129 / 78125000 :=
  shared_draw_failure_exact false
example : sharedDrawFailureProbability true = 52328129 / 78125000 :=
  shared_draw_failure_exact true
example (sent : Bool) : 1 / 2 < sharedDrawFailureProbability sent :=
  shared_draw_failure_large sent

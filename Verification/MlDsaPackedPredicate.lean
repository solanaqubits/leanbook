/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Std
import Init.Data.Nat.Bitwise

/-! Exact natural-number model of x2::pt5 at the frozen ML-DSA-44 leader.
The 23-bit input premise is essential. This does not model the whole verifier,
SHAKE, the Cairo compiler, or the surrounding caller invariants. -/

namespace MlDsaPackedPredicate

/-- Five 24-bit slots plus the exact Cairo offset, 8191 in each slot. -/
def packedSum (c0 c1 c2 c3 c4 : Nat) : Nat :=
  c0 + c1 * 16777216 + c2 * 281474976710656 +
  c3 * 4722366482869645213696 + c4 * 79228162514264337593543950336 +
  648957917835245355975654101753855

/-- The mask selects bit 23 in each 24-bit slot. -/
def mask : Nat := 0x800000800000800000800000800000

/-- Exact non-wrapping arithmetic expression in the Cairo helper. -/
def pt5 (c0 c1 c2 c3 c4 : Nat) : Nat := packedSum c0 c1 c2 c3 c4 &&& mask

/-- A mask of one bit is zero precisely when that bit is false. -/
theorem and_pow_zero_iff (x n : Nat) :
    x &&& 2 ^ n = 0 ↔ x.testBit n = false := by
  constructor
  · intro h
    have hb := congrArg (fun v : Nat => v.testBit n) h
    simpa using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hn : n = i
    · subst i
      simp [h]
    · simp [hn]

/-- Decomposition of the literal mask; checked by kernel reduction. -/
theorem mask_decomposition :
    mask = 2^23 ||| 2^47 ||| 2^71 ||| 2^95 ||| 2^119 := by decide

/-- Exact bit interpretation of the sparse literal mask. -/
theorem mask_zero_iff (x : Nat) :
    x &&& mask = 0 ↔
    x.testBit 23 = false ∧ x.testBit 47 = false ∧
    x.testBit 71 = false ∧ x.testBit 95 = false ∧ x.testBit 119 = false := by
  rw [mask_decomposition]
  simp only [Nat.and_or_distrib_left, Nat.or_eq_zero_iff, and_pow_zero_iff]
  simp only [and_assoc]

/-- The offset does not carry out of a 24-bit lane under the 23-bit premise. -/
theorem lane_no_carry (c : Nat) (hc : c < 8388608) : c + 8191 < 16777216 := by omega

/-- The selected high bit detects the exact ML-DSA modulus boundary. -/
theorem lane_threshold (c : Nat) (hc : c < 8388608) :
    (c + 8191).testBit 23 = false ↔ c < 8380417 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change decide ((c + 8191) / 8388608 % 2 = 1) = false ↔ c < 8380417
  simp only [decide_eq_false_iff_not]
  omega

/-- The expression fits a Cairo u128, so no u128 wrap is needed. -/
theorem packed_fits_u128 (a b c d e : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 8388608)
    (hd : d < 8388608) (he : e < 8388608) :
    packedSum a b c d e < 340282366920938463463374607431768211456 := by
  unfold packedSum
  omega

/-- The same integer is below the Cairo felt252 prime. -/
theorem packed_fits_felt (a b c d e : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 8388608)
    (hd : d < 8388608) (he : e < 8388608) :
    packedSum a b c d e <
      3618502788666131213697322783095070105623107215331596699973092056135872020481 := by
  have h := packed_fits_u128 a b c d e ha hb hc hd he
  omega

/-- Every lane's selected bit is preserved by packing; the result is exact. -/
theorem packed_bits (a b c d e : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 8388608)
    (hd : d < 8388608) (he : e < 8388608) :
    ((packedSum a b c d e).testBit 23 = false ↔ a < 8380417) ∧
    ((packedSum a b c d e).testBit 47 = false ↔ b < 8380417) ∧
    ((packedSum a b c d e).testBit 71 = false ↔ c < 8380417) ∧
    ((packedSum a b c d e).testBit 95 = false ↔ d < 8380417) ∧
    ((packedSum a b c d e).testBit 119 = false ↔ e < 8380417) := by
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not, packedSum]
  change ((_ / 8388608 % 2 ≠ 1) ↔ _) ∧ ((_ / 140737488355328 % 2 ≠ 1) ↔ _) ∧ ((_ / 2361183241434822606848 % 2 ≠ 1) ↔ _) ∧ ((_ / 39614081257132168796771975168 % 2 ≠ 1) ↔ _) ∧ ((_ / 664613997892457936451903530140172288 % 2 ≠ 1) ↔ _)
  omega

/-- Zero of the exact packed predicate is equivalent to accepting all five coefficients. -/
theorem pt5_zero_iff (a b c d e : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 8388608)
    (hd : d < 8388608) (he : e < 8388608) :
    pt5 a b c d e = 0 ↔
    a < 8380417 ∧ b < 8380417 ∧ c < 8380417 ∧ d < 8380417 ∧ e < 8380417 := by
  rw [pt5, mask_zero_iff]
  have h := packed_bits a b c d e ha hb hc hd he
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2]

/-- The result is bounded by its sparse mask, independently of the inputs. -/
theorem pt5_le_mask (a b c d e : Nat) : pt5 a b c d e ≤ mask := Nat.and_le_right

/-- Three nonnegative masked values cannot cancel modulo the Cairo prime. -/
theorem three_masks_no_cancellation (x y z : Nat)
    (hx : x ≤ mask) (hy : y ≤ mask) (hz : z ≤ mask) :
    (x + y + z) %
      3618502788666131213697322783095070105623107215331596699973092056135872020481 = 0 ↔
      x = 0 ∧ y = 0 ∧ z = 0 := by
  have h : x + y + z <
      3618502788666131213697322783095070105623107215331596699973092056135872020481 := by
    unfold mask at *
    omega
  rw [Nat.mod_eq_of_lt h]
  omega

/-- The 23-bit premise cannot be replaced by the declared 24-bit argument type. -/
theorem counterexample_without_23_bit_premise :
    pt5 16777215 0 0 0 0 = 0 ∧ ¬ (16777215 < 8380417) := by decide

/-- A bit window extracted after masking, using the same divide/remainder operations as uaa. -/
def window (word mask shift width : Nat) : Nat := (word &&& mask) / 2^shift % 2^width

/-- Every extracted window is bounded by the corresponding window of the mask. -/
theorem window_le_mask (word mask shift width : Nat) :
    window word mask shift width ≤ mask / 2^shift % 2^width := by
  unfold window
  rw [Nat.and_div_two_pow, Nat.and_mod_two_pow]
  exact Nat.and_le_right

/-- Eight coefficients formed from one of the two lanes of three masked words.
`shift = 0` selects the low lane and `shift = 64` selects the high lane. -/
def unpack8 (w0 w1 w2 shift : Nat) : List Nat :=
  [window w0 0xffff7fffff7fffffffff7fffff7fffff shift 24,
   window w0 0xffff7fffff7fffffffff7fffff7fffff (shift+24) 24,
   window w0 0xffff7fffff7fffffffff7fffff7fffff (shift+48) 16 +
     window w1 0xff7fffff7fffff7fff7fffff7fffff7f shift 8 * 65536,
   window w1 0xff7fffff7fffff7fff7fffff7fffff7f (shift+8) 24,
   window w1 0xff7fffff7fffff7fff7fffff7fffff7f (shift+32) 24,
   window w1 0xff7fffff7fffff7fff7fffff7fffff7f (shift+56) 8 +
     window w2 0x7fffff7fffff7fff7fffff7fffff7fff shift 16 * 256,
   window w2 0x7fffff7fffff7fff7fffff7fffff7fff (shift+16) 24,
   window w2 0x7fffff7fffff7fff7fffff7fffff7fff (shift+40) 24]

/-- Exact source masks force all eight low-lane coefficients into 23 bits. -/
theorem unpack8_low_bounded (w0 w1 w2 : Nat) :
    ∀ c ∈ unpack8 w0 w1 w2 0, c < 8388608 := by
  have h0 := window_le_mask w0 340279770772354453544649528911744466943 0 24
  change window w0 340279770772354453544649528911744466943 0 24 ≤ 8388607 at h0
  have h1 := window_le_mask w0 340279770772354453544649528911744466943 24 24
  change window w0 340279770772354453544649528911744466943 24 24 ≤ 8388607 at h1
  have h2 := window_le_mask w0 340279770772354453544649528911744466943 48 16
  change window w0 340279770772354453544649528911744466943 48 16 ≤ 65535 at h2
  have h3 := window_le_mask w1 339617752883431921908571264870867009407 0 8
  change window w1 339617752883431921908571264870867009407 0 8 ≤ 127 at h3
  have h4 := window_le_mask w1 339617752883431921908571264870867009407 8 24
  change window w1 339617752883431921908571264870867009407 8 24 ≤ 8388607 at h4
  have h5 := window_le_mask w1 339617752883431921908571264870867009407 32 24
  change window w1 339617752883431921908571264870867009407 32 24 ≤ 8388607 at h5
  have h6 := window_le_mask w1 339617752883431921908571264870867009407 56 8
  change window w1 339617752883431921908571264870867009407 56 8 ≤ 255 at h6
  have h7 := window_le_mask w2 170141173319263825433718911841060487167 0 16
  change window w2 170141173319263825433718911841060487167 0 16 ≤ 32767 at h7
  have h8 := window_le_mask w2 170141173319263825433718911841060487167 16 24
  change window w2 170141173319263825433718911841060487167 16 24 ≤ 8388607 at h8
  have h9 := window_le_mask w2 170141173319263825433718911841060487167 40 24
  change window w2 170141173319263825433718911841060487167 40 24 ≤ 8388607 at h9
  intro c hc
  simp only [unpack8, List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [Nat.reduceAdd] at hc
  rcases hc with h | h | h | h | h | h | h | h <;> subst c <;> omega

/-- Exact source masks force all eight high-lane coefficients into 23 bits. -/
theorem unpack8_high_bounded (w0 w1 w2 : Nat) :
    ∀ c ∈ unpack8 w0 w1 w2 64, c < 8388608 := by
  have h0 := window_le_mask w0 340279770772354453544649528911744466943 64 24
  change window w0 340279770772354453544649528911744466943 64 24 ≤ 8388607 at h0
  have h1 := window_le_mask w0 340279770772354453544649528911744466943 88 24
  change window w0 340279770772354453544649528911744466943 88 24 ≤ 8388607 at h1
  have h2 := window_le_mask w0 340279770772354453544649528911744466943 112 16
  change window w0 340279770772354453544649528911744466943 112 16 ≤ 65535 at h2
  have h3 := window_le_mask w1 339617752883431921908571264870867009407 64 8
  change window w1 339617752883431921908571264870867009407 64 8 ≤ 127 at h3
  have h4 := window_le_mask w1 339617752883431921908571264870867009407 72 24
  change window w1 339617752883431921908571264870867009407 72 24 ≤ 8388607 at h4
  have h5 := window_le_mask w1 339617752883431921908571264870867009407 96 24
  change window w1 339617752883431921908571264870867009407 96 24 ≤ 8388607 at h5
  have h6 := window_le_mask w1 339617752883431921908571264870867009407 120 8
  change window w1 339617752883431921908571264870867009407 120 8 ≤ 255 at h6
  have h7 := window_le_mask w2 170141173319263825433718911841060487167 64 16
  change window w2 170141173319263825433718911841060487167 64 16 ≤ 32767 at h7
  have h8 := window_le_mask w2 170141173319263825433718911841060487167 80 24
  change window w2 170141173319263825433718911841060487167 80 24 ≤ 8388607 at h8
  have h9 := window_le_mask w2 170141173319263825433718911841060487167 104 24
  change window w2 170141173319263825433718911841060487167 104 24 ≤ 8388607 at h9
  intro c hc
  simp only [unpack8, List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [Nat.reduceAdd] at hc
  rcases hc with h | h | h | h | h | h | h | h <;> subst c <;> omega


/-- Registry of selected arithmetic obligations; no whole-signature security claim. -/
structure MlDsaPackedPredicateSuite : Prop where
  pt5_zero_iff (a b c d e : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 8388608)
    (hd : d < 8388608) (he : e < 8388608) :
    pt5 a b c d e = 0 ↔
    a < 8380417 ∧ b < 8380417 ∧ c < 8380417 ∧ d < 8380417 ∧ e < 8380417
  packed_fits_u128 (a b c d e : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 8388608)
    (hd : d < 8388608) (he : e < 8388608) :
    packedSum a b c d e < 340282366920938463463374607431768211456
  unpack8_low_bounded (w0 w1 w2 : Nat) :
    ∀ c ∈ unpack8 w0 w1 w2 0, c < 8388608
  unpack8_high_bounded (w0 w1 w2 : Nat) :
    ∀ c ∈ unpack8 w0 w1 w2 64, c < 8388608
  counterexample_without_23_bit_premise :
    pt5 16777215 0 0 0 0 = 0 ∧ ¬ (16777215 < 8380417)

/-- Package the already proved obligations for the cryptography registry. -/
theorem verification_suite : MlDsaPackedPredicateSuite := {
  pt5_zero_iff := @pt5_zero_iff
  packed_fits_u128 := @packed_fits_u128
  unpack8_low_bounded := @unpack8_low_bounded
  unpack8_high_bounded := @unpack8_high_bounded
  counterexample_without_23_bit_premise := @counterexample_without_23_bit_premise
}

end MlDsaPackedPredicate

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaPackedPredicate

/-! Exact wt arithmetic by 64-bit lanes, with explicit bounds and a source map.
No Cairo operational or compiler semantics are asserted. -/
namespace MlDsaWtBranch
open MlDsaPackedPredicate

def wt (w k t : Nat) : Nat := (w + k) &&& t

/-- Bitwise AND acts independently on two non-overlapping 64-bit lanes. -/
theorem and_lanes (lo hi t : Nat) (hl : lo < 2^64) (ht : t < 2^64) :
    (2^64 * hi + lo) &&& (2^64 * t + t) =
      2^64 * (hi &&& t) + (lo &&& t) := by
  have hb : lo &&& t < 2^64 := Nat.lt_of_le_of_lt Nat.and_le_left hl
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow_mul_add hi hl,
    Nat.testBit_two_pow_mul_add t ht, Nat.testBit_two_pow_mul_add (hi &&& t) hb]
  by_cases h : i < 64 <;> simp [h]

/-- When adding the offset cannot carry across the lane boundary, wt splits exactly. -/
theorem wt_lanes (lo hi k t : Nat) (hl : lo+k < 2^64) (ht : t < 2^64) :
    wt (2^64*hi+lo) (2^64*k+k) (2^64*t+t) =
      2^64 * wt hi k t + wt lo k t := by
  unfold wt
  have e : 2^64*hi+lo+(2^64*k+k) = 2^64*(hi+k)+(lo+k) := by
    simp only [Nat.mul_add]
    ac_rfl
  rw [e]
  exact and_lanes (lo+k) (hi+k) t hl ht

/-- Zero of the combined signal means zero in both lanes. -/
theorem wt_lanes_zero_iff (lo hi k t : Nat) (hl : lo+k < 2^64) (ht : t < 2^64) :
    wt (2^64*hi+lo) (2^64*k+k) (2^64*t+t) = 0 ↔
      wt lo k t = 0 ∧ wt hi k t = 0 := by
  rw [wt_lanes lo hi k t hl ht]
  rw [Nat.add_eq_zero_iff, Nat.mul_eq_zero]
  simp [and_comm]


/-- A bit below a digit boundary is independent of all higher digits. -/
theorem low_bit (d upper width bit : Nat) (hd : d < 2^width) (hb : bit < width) :
    (2^width*upper+d).testBit bit = d.testBit bit := by
  rw [Nat.testBit_two_pow_mul_add upper hd, if_pos hb]

/-- A bit above a digit boundary is a bit of the quotient. -/
theorem high_bit (d upper width bit : Nat) (hd : d < 2^width) (hb : ¬ bit < width) :
    (2^width*upper+d).testBit bit = upper.testBit (bit-width) := by
  rw [Nat.testBit_two_pow_mul_add upper hd, if_neg hb]

theorem byte_threshold (a : Nat) (ha : a < 128) :
    (a+1).testBit 7 = false ↔ a < 127 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change decide ((a+1)/128%2=1)=false ↔ a<127
  rw [decide_eq_false_iff_not]
  omega

theorem halfword_threshold (a : Nat) (ha : a < 32768) :
    (a+32).testBit 15 = false ↔ a < 32736 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change decide ((a+32)/32768%2=1)=false ↔ a<32736
  rw [decide_eq_false_iff_not]
  omega

/-- The source word layout within one 64-bit lane. -/
def lane0 (a b c : Nat) : Nat :=
  a + 16777216 * b + 281474976710656 * c

/-- Offset addition cannot carry to the adjacent lane. -/
theorem lane0_fits (a b c : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 65536) :
    lane0 a b c + 137422184447 < 18446744073709551616 := by
  unfold lane0
  omega

/-- Exact coarse thresholds for this lane layout. -/
theorem lane0_offset (a b c : Nat)
    (_ha : a < 8388608) (_hb : b < 8388608) (_hc : c < 65536) : lane0 a b c + 137422184447 = (2^24*((2^24*(c)+(b+8191)))+(a+8191)) := by
  unfold lane0
  change _ = (16777216*((16777216*(c)+(b+8191)))+(a+8191))
  omega


theorem lane0_bit0 (a b c : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 65536) : (lane0 a b c + 137422184447).testBit 23 = false ↔ a < 8380417 := by
  have repr := lane0_offset a b c ha hb hc
  have d0 : a+8191 < 2^24 := by change a+8191 < 16777216; omega
  rw [repr]
  rw [low_bit (a+8191) ((2^24*(c)+(b+8191))) 24 23 d0 (by decide)]
  exact lane_threshold a ha

theorem lane0_bit1 (a b c : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 65536) : (lane0 a b c + 137422184447).testBit 47 = false ↔ b < 8380417 := by
  have repr := lane0_offset a b c ha hb hc
  have d0 : a+8191 < 2^24 := by change a+8191 < 16777216; omega
  have d1 : b+8191 < 2^24 := by change b+8191 < 16777216; omega
  rw [repr]
  rw [high_bit (a+8191) ((2^24*(c)+(b+8191))) 24 47 d0 (by decide)]
  change ((2^24*(c)+(b+8191))).testBit 23 = false ↔ b < 8380417
  rw [low_bit (b+8191) (c) 24 23 d1 (by decide)]
  exact lane_threshold b hb

theorem mask0_decomposition : (140737496743936 : Nat) = 2^23 ||| 2^47 := by decide

theorem mask0_zero_iff (x : Nat) :
    x &&& 140737496743936 = 0 ↔ x.testBit 23 = false ∧ x.testBit 47 = false := by
  rw [mask0_decomposition]
  simp only [Nat.and_or_distrib_left, Nat.or_eq_zero_iff, and_pow_zero_iff]

theorem wt0_lane_zero_iff (a b c : Nat)
    (ha : a < 8388608) (hb : b < 8388608) (hc : c < 65536) :
    wt (lane0 a b c) 137422184447 140737496743936 = 0 ↔ a < 8380417 ∧ b < 8380417 := by
  rw [wt, mask0_zero_iff]
  rw [lane0_bit0 a b c ha hb hc, lane0_bit1 a b c ha hb hc]

/-- Source u128 constants are duplicated 64-bit lane constants. -/
theorem source_constants_0 :
    (2534991866543918165817041100799 : Nat) = 2^64*137422184447+137422184447 ∧
    (2596148584009918725078520023744512 : Nat) = 2^64*140737496743936+140737496743936 := by decide

/-- The source word layout within one 64-bit lane. -/
def lane1 (a b c d : Nat) : Nat :=
  a + 256 * b + 4294967296 * c + 72057594037927936 * d

/-- Offset addition cannot carry to the adjacent lane. -/
theorem lane1_fits (a b c d : Nat)
    (ha : a < 128) (hb : b < 8388608) (hc : c < 8388608) (hd : d < 256) :
    lane1 a b c d + 35180079218433 < 18446744073709551616 := by
  unfold lane1
  omega

/-- Exact coarse thresholds for this lane layout. -/
theorem lane1_offset (a b c d : Nat)
    (_ha : a < 128) (_hb : b < 8388608) (_hc : c < 8388608) (_hd : d < 256) : lane1 a b c d + 35180079218433 = (2^8*((2^24*((2^24*(d)+(c+8191)))+(b+8191)))+(a+1)) := by
  unfold lane1
  change _ = (256*((16777216*((16777216*(d)+(c+8191)))+(b+8191)))+(a+1))
  omega


theorem lane1_bit0 (a b c d : Nat)
    (ha : a < 128) (hb : b < 8388608) (hc : c < 8388608) (hd : d < 256) : (lane1 a b c d + 35180079218433).testBit 7 = false ↔ a < 127 := by
  have repr := lane1_offset a b c d ha hb hc hd
  have d0 : a+1 < 2^8 := by change a+1 < 256; omega
  rw [repr]
  rw [low_bit (a+1) ((2^24*((2^24*(d)+(c+8191)))+(b+8191))) 8 7 d0 (by decide)]
  exact byte_threshold a ha

theorem lane1_bit1 (a b c d : Nat)
    (ha : a < 128) (hb : b < 8388608) (hc : c < 8388608) (hd : d < 256) : (lane1 a b c d + 35180079218433).testBit 31 = false ↔ b < 8380417 := by
  have repr := lane1_offset a b c d ha hb hc hd
  have d0 : a+1 < 2^8 := by change a+1 < 256; omega
  have d1 : b+8191 < 2^24 := by change b+8191 < 16777216; omega
  rw [repr]
  rw [high_bit (a+1) ((2^24*((2^24*(d)+(c+8191)))+(b+8191))) 8 31 d0 (by decide)]
  change ((2^24*((2^24*(d)+(c+8191)))+(b+8191))).testBit 23 = false ↔ b < 8380417
  rw [low_bit (b+8191) ((2^24*(d)+(c+8191))) 24 23 d1 (by decide)]
  exact lane_threshold b hb

theorem lane1_bit2 (a b c d : Nat)
    (ha : a < 128) (hb : b < 8388608) (hc : c < 8388608) (hd : d < 256) : (lane1 a b c d + 35180079218433).testBit 55 = false ↔ c < 8380417 := by
  have repr := lane1_offset a b c d ha hb hc hd
  have d0 : a+1 < 2^8 := by change a+1 < 256; omega
  have d1 : b+8191 < 2^24 := by change b+8191 < 16777216; omega
  have d2 : c+8191 < 2^24 := by change c+8191 < 16777216; omega
  rw [repr]
  rw [high_bit (a+1) ((2^24*((2^24*(d)+(c+8191)))+(b+8191))) 8 55 d0 (by decide)]
  change ((2^24*((2^24*(d)+(c+8191)))+(b+8191))).testBit 47 = false ↔ c < 8380417
  rw [high_bit (b+8191) ((2^24*(d)+(c+8191))) 24 47 d1 (by decide)]
  change ((2^24*(d)+(c+8191))).testBit 23 = false ↔ c < 8380417
  rw [low_bit (c+8191) (d) 24 23 d2 (by decide)]
  exact lane_threshold c hc

theorem mask1_decomposition : (36028799166447744 : Nat) = 2^7 ||| 2^31 ||| 2^55 := by decide

theorem mask1_zero_iff (x : Nat) :
    x &&& 36028799166447744 = 0 ↔ x.testBit 7 = false ∧ x.testBit 31 = false ∧ x.testBit 55 = false := by
  rw [mask1_decomposition]
  simp only [Nat.and_or_distrib_left, Nat.or_eq_zero_iff, and_pow_zero_iff, and_assoc]

theorem wt1_lane_zero_iff (a b c d : Nat)
    (ha : a < 128) (hb : b < 8388608) (hc : c < 8388608) (hd : d < 256) :
    wt (lane1 a b c d) 35180079218433 36028799166447744 = 0 ↔ a < 127 ∧ b < 8380417 ∧ c < 8380417 := by
  rw [wt, mask1_zero_iff]
  rw [lane1_bit0 a b c d ha hb hc hd, lane1_bit1 a b c d ha hb hc hd, lane1_bit2 a b c d ha hb hc hd]

/-- Source u128 constants are duplicated 64-bit lane constants. -/
theorem source_constants_1 :
    (648957917835261497193236231356161 : Nat) = 2^64*35180079218433+35180079218433 ∧
    (664614037506541554803342560901202048 : Nat) = 2^64*36028799166447744+36028799166447744 := by decide

/-- The source word layout within one 64-bit lane. -/
def lane2 (a b c : Nat) : Nat :=
  a + 65536 * b + 1099511627776 * c

/-- Offset addition cannot carry to the adjacent lane. -/
theorem lane2_fits (a b c : Nat)
    (ha : a < 32768) (hb : b < 8388608) (hc : c < 8388608) :
    lane2 a b c + 9006100279918624 < 18446744073709551616 := by
  unfold lane2
  omega

/-- Exact coarse thresholds for this lane layout. -/
theorem lane2_offset (a b c : Nat)
    (_ha : a < 32768) (_hb : b < 8388608) (_hc : c < 8388608) : lane2 a b c + 9006100279918624 = (2^16*((2^24*((2^24*(0)+(c+8191)))+(b+8191)))+(a+32)) := by
  unfold lane2
  change _ = (65536*((16777216*((16777216*(0)+(c+8191)))+(b+8191)))+(a+32))
  omega


theorem lane2_bit0 (a b c : Nat)
    (ha : a < 32768) (hb : b < 8388608) (hc : c < 8388608) : (lane2 a b c + 9006100279918624).testBit 15 = false ↔ a < 32736 := by
  have repr := lane2_offset a b c ha hb hc
  have d0 : a+32 < 2^16 := by change a+32 < 65536; omega
  rw [repr]
  rw [low_bit (a+32) ((2^24*((2^24*(0)+(c+8191)))+(b+8191))) 16 15 d0 (by decide)]
  exact halfword_threshold a ha

theorem lane2_bit1 (a b c : Nat)
    (ha : a < 32768) (hb : b < 8388608) (hc : c < 8388608) : (lane2 a b c + 9006100279918624).testBit 39 = false ↔ b < 8380417 := by
  have repr := lane2_offset a b c ha hb hc
  have d0 : a+32 < 2^16 := by change a+32 < 65536; omega
  have d1 : b+8191 < 2^24 := by change b+8191 < 16777216; omega
  rw [repr]
  rw [high_bit (a+32) ((2^24*((2^24*(0)+(c+8191)))+(b+8191))) 16 39 d0 (by decide)]
  change ((2^24*((2^24*(0)+(c+8191)))+(b+8191))).testBit 23 = false ↔ b < 8380417
  rw [low_bit (b+8191) ((2^24*(0)+(c+8191))) 24 23 d1 (by decide)]
  exact lane_threshold b hb

theorem lane2_bit2 (a b c : Nat)
    (ha : a < 32768) (hb : b < 8388608) (hc : c < 8388608) : (lane2 a b c + 9006100279918624).testBit 63 = false ↔ c < 8380417 := by
  have repr := lane2_offset a b c ha hb hc
  have d0 : a+32 < 2^16 := by change a+32 < 65536; omega
  have d1 : b+8191 < 2^24 := by change b+8191 < 16777216; omega
  have d2 : c+8191 < 2^24 := by change c+8191 < 16777216; omega
  rw [repr]
  rw [high_bit (a+32) ((2^24*((2^24*(0)+(c+8191)))+(b+8191))) 16 63 d0 (by decide)]
  change ((2^24*((2^24*(0)+(c+8191)))+(b+8191))).testBit 47 = false ↔ c < 8380417
  rw [high_bit (b+8191) ((2^24*(0)+(c+8191))) 24 47 d1 (by decide)]
  change ((2^24*(0)+(c+8191))).testBit 23 = false ↔ c < 8380417
  rw [low_bit (c+8191) (0) 24 23 d2 (by decide)]
  exact lane_threshold c hc

theorem mask2_decomposition : (9223372586610622464 : Nat) = 2^15 ||| 2^39 ||| 2^63 := by decide

theorem mask2_zero_iff (x : Nat) :
    x &&& 9223372586610622464 = 0 ↔ x.testBit 15 = false ∧ x.testBit 39 = false ∧ x.testBit 63 = false := by
  rw [mask2_decomposition]
  simp only [Nat.and_or_distrib_left, Nat.or_eq_zero_iff, and_pow_zero_iff, and_assoc]

theorem wt2_lane_zero_iff (a b c : Nat)
    (ha : a < 32768) (hb : b < 8388608) (hc : c < 8388608) :
    wt (lane2 a b c) 9006100279918624 9223372586610622464 = 0 ↔ a < 32736 ∧ b < 8380417 ∧ c < 8380417 := by
  rw [wt, mask2_zero_iff]
  rw [lane2_bit0 a b c ha hb hc, lane2_bit1 a b c ha hb hc, lane2_bit2 a b c ha hb hc]

/-- Source u128 constants are duplicated 64-bit lane constants. -/
theorem source_constants_2 :
    (166133226965822811210795964287615008 : Nat) = 2^64*9006100279918624+9006100279918624 ∧
    (170141193601674638029655695590707724288 : Nat) = 2^64*9223372586610622464+9223372586610622464 := by decide
/-- The source mask suffices to prevent the wt conversion to u128 from overflowing. -/
theorem masked_word0_fits (w : Nat) :
    (w &&& 340279770772354453544649528911744466943) + 2534991866543918165817041100799 < 340282366920938463463374607431768211456 := by
  have h : w &&& 340279770772354453544649528911744466943 ≤ 340279770772354453544649528911744466943 := Nat.and_le_right
  omega

/-- The source mask suffices to prevent the wt conversion to u128 from overflowing. -/
theorem masked_word1_fits (w : Nat) :
    (w &&& 339617752883431921908571264870867009407) + 648957917835261497193236231356161 < 340282366920938463463374607431768211456 := by
  have h : w &&& 339617752883431921908571264870867009407 ≤ 339617752883431921908571264870867009407 := Nat.and_le_right
  omega

/-- The source mask suffices to prevent the wt conversion to u128 from overflowing. -/
theorem masked_word2_fits (w : Nat) :
    (w &&& 170141173319263825433718911841060487167) + 166133226965822811210795964287615008 < 340282366920938463463374607431768211456 := by
  have h : w &&& 170141173319263825433718911841060487167 ≤ 170141173319263825433718911841060487167 := Nat.and_le_right
  omega

/-- The c2 high-byte test is conservative: no false negatives at q. -/
theorem split_c2_sound (c : Nat) (hc : c < 8388608) :
    c / 65536 < 127 → c < 8380417 := by omega

/-- The c5 high-word test is conservative: no false negatives at q. -/
theorem split_c5_sound (c : Nat) (hc : c < 8388608) :
    c / 256 < 32736 → c < 8380417 := by omega

/-- A c2 false positive can occur on this whole valid interval. -/
theorem split_c2_false_positive_iff (c : Nat) (hc : c < 8388608) :
    (¬ c / 65536 < 127) ∧ c < 8380417 ↔ 8323072 ≤ c ∧ c < 8380417 := by omega

/-- For c5 the only valid false positive is q-1. -/
theorem split_c5_false_positive_iff (c : Nat) (hc : c < 8388608) :
    (¬ c / 256 < 32736) ∧ c < 8380417 ↔ c = 8380416 := by omega

/-- Formal counterexamples to interpreting wt as an exact per-coefficient q check. -/
theorem conservative_not_exact :
    8323072 < 8380417 ∧ ¬ (8323072 / 65536 < 127) ∧
    8380416 < 8380417 ∧ ¬ (8380416 / 256 < 32736) := by decide


/-- The low lane of a source wt mask occupies only the bottom 64 bits. -/
theorem wt_low_bound (w k t : Nat)
    (ht : t % 2361183241434822606848 < 18446744073709551616) :
    wt w k t % 2361183241434822606848 < 18446744073709551616 := by
  unfold wt
  change ((w+k) &&& t) % 2^71 < _
  rw [Nat.and_mod_two_pow]
  exact Nat.lt_of_le_of_lt Nat.and_le_right ht

/-- All three literal source masks satisfy the low-lane bound. -/
theorem source_masks_low_bound :
    2596148584009918725078520023744512 % 2361183241434822606848 < 18446744073709551616 ∧
    664614037506541554803342560901202048 % 2361183241434822606848 < 18446744073709551616 ∧
    170141193601674638029655695590707724288 % 2361183241434822606848 < 18446744073709551616 := by decide

/-- A finite sum is bounded by its length times a uniform nonnegative bound. -/
theorem sum_bounded (xs : List Nat) (bound : Nat) (h : ∀ x ∈ xs, x ≤ bound) :
    xs.sum ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- At most 21 wt values are accumulated by the 56-coefficient path; no field wrap occurs. -/
theorem sum_fits_felt (xs : List Nat) (hn : xs.length ≤ 21)
    (h : ∀ x ∈ xs, x < 340282366920938463463374607431768211456) :
    xs.sum < 3618502788666131213697322783095070105623107215331596699973092056135872020481 := by
  have hs := sum_bounded xs 340282366920938463463374607431768211455
    (fun x hx => by have := h x hx; omega)
  omega

/-- The sum of all low contributions stays below the 2^71 lane separator. -/
theorem low_sum_fits (xs : List Nat) (hn : xs.length ≤ 21)
    (h : ∀ x ∈ xs, x % 2361183241434822606848 < 18446744073709551616) :
    (xs.map (fun x => x % 2361183241434822606848)).sum < 2361183241434822606848 := by
  have hs := sum_bounded (xs.map (fun x => x % 2361183241434822606848)) 18446744073709551615
    (by
      intro y hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      have := h x hx
      omega)
  simp only [List.length_map] at hs
  omega

/-- Reducing a finite sum is the same as summing its residues and reducing once. -/
theorem sum_mod_map (xs : List Nat) (m : Nat) :
    xs.sum % m = (xs.map (fun x => x % m)).sum % m := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Nat.add_mod, ih]

/-- Thus af on a whole source block is exactly the sum of its low signals. -/
theorem low_sum_exact (xs : List Nat) (hn : xs.length ≤ 21)
    (h : ∀ x ∈ xs, x % 2361183241434822606848 < 18446744073709551616) :
    xs.sum % 2361183241434822606848 =
      (xs.map (fun x => x % 2361183241434822606848)).sum := by
  rw [sum_mod_map]
  exact Nat.mod_eq_of_lt (low_sum_fits xs hn h)

/-- Reading only low u128 before taking af does not lose a low-lane signal. -/
theorem af_u128_projection (r : Nat) :
    r % 340282366920938463463374607431768211456 % 2361183241434822606848 =
      r % 2361183241434822606848 := by
  exact Nat.mod_mod_of_dvd r (by decide)

/-- Equal low prefixes mean that the added block contributes zero low signal, without wrap. -/
theorem low_prefix_equal_iff (pref delta : Nat)
    (h : pref % 2361183241434822606848 + delta % 2361183241434822606848 < 2361183241434822606848) :
    (pref+delta) % 2361183241434822606848 = pref % 2361183241434822606848 ↔
      delta % 2361183241434822606848 = 0 := by
  rw [Nat.add_mod, Nat.mod_eq_of_lt h]
  omega

/-- bcl is exactly the absence of a high contribution in this nonnegative encoding. -/
theorem high_clear_iff (r : Nat) :
    r < 2361183241434822606848 ↔ r / 2361183241434822606848 = 0 := by omega

/-- Prefix subtraction in the field equals the nonnegative added block under the no-wrap bound. -/
theorem field_prefix_difference (pref delta : Nat)
    (h : pref+delta < 3618502788666131213697322783095070105623107215331596699973092056135872020481) :
    ((pref+delta) % 3618502788666131213697322783095070105623107215331596699973092056135872020481 +
      3618502788666131213697322783095070105623107215331596699973092056135872020481 - pref) %
      3618502788666131213697322783095070105623107215331596699973092056135872020481 = delta := by
  rw [Nat.mod_eq_of_lt h]
  have e : pref+delta+3618502788666131213697322783095070105623107215331596699973092056135872020481-pref =
    delta+3618502788666131213697322783095070105623107215331596699973092056135872020481 := by omega
  rw [e, Nat.add_mod]
  have hd : delta < 3618502788666131213697322783095070105623107215331596699973092056135872020481 := by omega
  simp [Nat.mod_eq_of_lt hd]

/-- ca's coarse low guard plus exact split-coefficient repair, with explicit signal premises. -/
theorem repair_low_exact (part full : Nat) (hp : part < 8388608)
    (valid : Prop) (hclear : part = 0 → valid) :
    (part+8388608*full < 8388608 ∧ (part+8388608*full = 0 ∨ valid)) ↔
      full = 0 ∧ valid := by
  have hf : part+8388608*full < 8388608 ↔ full=0 := by omega
  rw [hf]
  constructor
  · rintro ⟨rfl, h | h⟩
    · exact ⟨rfl, hclear (by omega)⟩
    · exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, Or.inr h⟩

/-- cb's upper-lane guard and repair, after decoding its separated signal fields. -/
theorem repair_high_exact (low part full : Nat)
    (hl : low < 2361183241434822606848) (hp : part < 65536)
    (valid : Prop) (hclear : part = 0 → valid) :
    (low+2361183241434822606848*(part+65536*full) < 154742504910672534362390528 ∧
      (low+2361183241434822606848*(part+65536*full) < 2361183241434822606848 ∨ valid)) ↔
      full=0 ∧ valid := by
  have hf : low+2361183241434822606848*(part+65536*full) < 154742504910672534362390528 ↔ full=0 := by omega
  have hz : low+2361183241434822606848*(part+65536*full) < 2361183241434822606848 ↔ part=0 ∧ full=0 := by omega
  rw [hf, hz]
  constructor
  · rintro ⟨hf, hz | hv⟩
    · exact ⟨hf, hclear hz.1⟩
    · exact ⟨hf, hv⟩
  · rintro ⟨hf, hv⟩
    exact ⟨hf, Or.inr hv⟩

/-- If a block has no rejected coefficient, appending it preserves exactly the filtered sequence. -/
theorem filter_identity (xs : List Nat) (h : ∀ x ∈ xs, x < 8380417) :
    xs.filter (fun x => decide (x < 8380417)) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp [hx, ht]


/-- Registry of selected arithmetic obligations; no whole-signature security claim. -/
structure MlDsaWtBranchSuite : Prop where
  wt_lanes_zero_iff (lo hi k t : Nat) (hl : lo+k < 2^64) (ht : t < 2^64) :
    wt (2^64*hi+lo) (2^64*k+k) (2^64*t+t) = 0 ↔
      wt lo k t = 0 ∧ wt hi k t = 0
  low_sum_exact (xs : List Nat) (hn : xs.length ≤ 21)
    (h : ∀ x ∈ xs, x % 2361183241434822606848 < 18446744073709551616) :
    xs.sum % 2361183241434822606848 =
      (xs.map (fun x => x % 2361183241434822606848)).sum
  repair_low_exact (part full : Nat) (hp : part < 8388608)
    (valid : Prop) (hclear : part = 0 → valid) :
    (part+8388608*full < 8388608 ∧ (part+8388608*full = 0 ∨ valid)) ↔
      full = 0 ∧ valid
  repair_high_exact (low part full : Nat)
    (hl : low < 2361183241434822606848) (hp : part < 65536)
    (valid : Prop) (hclear : part = 0 → valid) :
    (low+2361183241434822606848*(part+65536*full) < 154742504910672534362390528 ∧
      (low+2361183241434822606848*(part+65536*full) < 2361183241434822606848 ∨ valid)) ↔
      full=0 ∧ valid
  filter_identity (xs : List Nat) (h : ∀ x ∈ xs, x < 8380417) :
    xs.filter (fun x => decide (x < 8380417)) = xs

/-- Package the already proved obligations for the cryptography registry. -/
theorem verification_suite : MlDsaWtBranchSuite := {
  wt_lanes_zero_iff := @wt_lanes_zero_iff
  low_sum_exact := @low_sum_exact
  repair_low_exact := @repair_low_exact
  repair_high_exact := @repair_high_exact
  filter_identity := @filter_identity
}

end MlDsaWtBranch

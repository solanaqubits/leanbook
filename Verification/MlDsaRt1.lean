/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Std
import Init.Data.Nat.Bitwise

/-! Natural-number models of Stage 15 rt/rt1 field expressions.
This module proves the exact arithmetic correspondence of rt/rt1 at pow=2
to two independent 64-bit rotations under the stated input and mask conditions.
It does not model Cairo libfunc execution or establish whole-verifier security. -/

namespace MlDsaRt1

/-- Modulus used by Cairo felt252; no primality hypothesis is needed below. -/
def cairoPrime : Nat := 2 ^ 251 + 17 * 2 ^ 192 + 1

/-- Exact multiplier in k2.cairo rt, line 7. -/
def cConstant : Nat := 0x80000000000001100000000000000000000000000000001

/-- Exact multiplier in k2.cairo rt1, line 13. -/
def dConstant : Nat := 0x100000000000002200000000000000000000000000000002

/-- Ss.g0.m0, selecting the two high bits of the 64-bit halves. -/
def rt1Mask : Nat := 0x80000000000000008000000000000000

/-- Low half of the packed word. -/
def low64 (w : Nat) : Nat := w % 2 ^ 64

/-- High half; its 64-bit bound requires a bound on w. -/
def high64 (w : Nat) : Nat := w / 2 ^ 64

/-- Arithmetic specification of rotation by one on a bounded 64-bit word. -/
def rotl64_1 (x : Nat) : Nat := x % 2 ^ 63 * 2 + x / 2 ^ 63

/-- Two independent half-word rotations, packed back into one natural. -/
def packRotl64_1 (w : Nat) : Nat :=
  rotl64_1 (low64 w) + 2 ^ 64 * rotl64_1 (high64 w)

/-- The input bound ensures each low half is a valid 64-bit word. -/
theorem low64_lt (w : Nat) : low64 w < 2 ^ 64 := by
  exact Nat.mod_lt _ (by decide)

/-- The high half is bounded if the input fits 128 bits. -/
theorem high64_lt {w : Nat} (hw : w < 2 ^ 128) : high64 w < 2 ^ 64 := by
  unfold high64
  omega

/-- Rotation preserves the unsigned 64-bit range. -/
theorem rotl64_1_lt {x : Nat} (hx : x < 2 ^ 64) : rotl64_1 x < 2 ^ 64 := by
  unfold rotl64_1
  omega

/-- Independent rotated halves fit the original 128-bit container. -/
theorem packRotl64_1_lt_u128 {w : Nat} (hw : w < 2 ^ 128) :
    packRotl64_1 w < 2 ^ 128 := by
  have hl := rotl64_1_lt (low64_lt w)
  have hh := rotl64_1_lt (high64_lt hw)
  unfold packRotl64_1
  omega

/-- Exact numeric relation, not a sampled input check. -/
theorem dConstant_eq_two_cConstant : dConstant = 2 * cConstant := by decide

/-- The modulus is positive. -/
theorem cairoPrime_pos : 0 < cairoPrime := by decide

/-- Both source literals are canonical residues. -/
theorem constants_lt_modulus : cConstant < cairoPrime ∧ dConstant < cairoPrime := by
  decide

/-- Constant identity needed for a future proof of rotation correspondence. -/
theorem dConstant_mul_half_mod :
    (dConstant * 2 ^ 63) % cairoPrime = 2 ^ 64 - 1 := by decide

/-- Natural subtraction cannot truncate when the subtrahend is a residue. -/
theorem residue_le_padded (w t : Nat) : t % cairoPrime ≤ w + cairoPrime := by
  have h := Nat.mod_lt t cairoPrime_pos
  omega

/-- Model of ((w - (w & ia) * C) * pow) in residues, with safe natural subtraction. -/
def rtFieldExpr (w ia pow : Nat) : Nat :=
  let t := w &&& ia
  let sub := (w + cairoPrime - (t * cConstant) % cairoPrime) % cairoPrime
  (sub * pow) % cairoPrime

/-- Model of w + w - (w & ia) * D in residues, with safe natural subtraction. -/
def rt1FieldExpr (w ia : Nat) : Nat :=
  let t := w &&& ia
  let sub := (w + w + cairoPrime - (t * dConstant) % cairoPrime) % cairoPrime
  sub % cairoPrime

/-- Equivalence for arbitrary natural inputs and masks at pow=2. -/
theorem rt1_eq_rt_pow2 (w ia : Nat) :
    rt1FieldExpr w ia = rtFieldExpr w ia 2 := by
  simp only [rt1FieldExpr, rtFieldExpr]
  dsimp [cairoPrime, cConstant, dConstant]
  omega

/-- Exact expansion of the mask selecting the two half-word high bits. -/
theorem rt1Mask_eq_sum : rt1Mask = 2 ^ 63 + 2 ^ 127 := by decide

/-- A bounded half-word masked at bit 63 is determined by its high-bit quotient. -/
theorem and_bit63_of_lt {x : Nat} (hx : x < 2 ^ 64) :
    x &&& 2 ^ 63 = 2 ^ 63 * (x / 2 ^ 63) := by
  have hm : (x &&& 2 ^ 63) % 2 ^ 63 = 0 := by
    rw [Nat.and_mod_two_pow]
    simp
  have hd : (x &&& 2 ^ 63) / 2 ^ 63 = x / 2 ^ 63 := by
    rw [Nat.and_div_two_pow]
    simp only [Nat.div_self (by decide : 0 < 2 ^ 63), Nat.and_one_is_mod]
    omega
  have h := Nat.mod_add_div (x &&& 2 ^ 63) (2 ^ 63)
  omega

/-- Exact extraction of bit 63 of each half of a bounded 128-bit word. -/
theorem land_rt1Mask_eq {w : Nat} (hw : w < 2 ^ 128) :
    w &&& rt1Mask =
      2 ^ 63 * (low64 w / 2 ^ 63 + 2 ^ 64 * (high64 w / 2 ^ 63)) := by
  have hm : (w &&& rt1Mask) % 2 ^ 64 = low64 w &&& 2 ^ 63 := by
    rw [Nat.and_mod_two_pow]
    rw [show rt1Mask % 2 ^ 64 = 2 ^ 63 by decide]
    rfl
  have hd : (w &&& rt1Mask) / 2 ^ 64 = high64 w &&& 2 ^ 63 := by
    rw [Nat.and_div_two_pow]
    rw [show rt1Mask / 2 ^ 64 = 2 ^ 63 by decide]
    rfl
  rw [and_bit63_of_lt (low64_lt w)] at hm
  rw [and_bit63_of_lt (high64_lt hw)] at hd
  have h := Nat.mod_add_div (w &&& rt1Mask) (2 ^ 64)
  omega

/-- Division-free packed identity; natural subtraction is avoided. -/
theorem packRotl64_1_linear_identity {w : Nat} (hw : w < 2 ^ 128) :
    2 ^ 63 * packRotl64_1 w + (2 ^ 64 - 1) * (w &&& rt1Mask) =
      2 ^ 63 * (2 * w) := by
  rw [land_rt1Mask_eq hw]
  unfold packRotl64_1 rotl64_1 low64 high64
  omega

/-- The exact residue model equals two independent half-word rotations. -/
theorem rt1FieldExpr_eq_packRotl64_1 {w : Nat} (hw : w < 2 ^ 128) :
    rt1FieldExpr w rt1Mask = packRotl64_1 w := by
  have hm := land_rt1Mask_eq hw
  have hl := packRotl64_1_linear_identity hw
  have hb := packRotl64_1_lt_u128 hw
  rw [hm] at hl
  unfold rt1FieldExpr
  rw [hm]
  dsimp [cairoPrime, dConstant]
  omega

/-- The canonical model result is the packed rotation and fits 128 bits. -/
theorem rt1FieldExpr_eq_packRotl64_1_and_lt {w : Nat} (hw : w < 2 ^ 128) :
    rt1FieldExpr w rt1Mask = packRotl64_1 w ∧ packRotl64_1 w < 2 ^ 128 := by
  exact ⟨rt1FieldExpr_eq_packRotl64_1 hw, packRotl64_1_lt_u128 hw⟩

/-- The original rt model at pow=2 has the same packed-rotation meaning. -/
theorem rtFieldExpr_pow2_eq_packRotl64_1 {w : Nat} (hw : w < 2 ^ 128) :
    rtFieldExpr w rt1Mask 2 = packRotl64_1 w := by
  rw [← rt1_eq_rt_pow2]
  exact rt1FieldExpr_eq_packRotl64_1 hw

end MlDsaRt1

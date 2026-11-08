import Verification.MlDsaRt1

/-! Kernel-checked boundaries and separation of independent half-word rotation
from a single 128-bit shift. Closed examples supplement the universal
field-expression-to-rotation theorem and check that its premises are essential. -/

open MlDsaRt1

example : dConstant = 2 * cConstant := dConstant_eq_two_cConstant
example : (dConstant * 2 ^ 63) % cairoPrime = 2 ^ 64 - 1 :=
  dConstant_mul_half_mod
example : low64 (2 ^ 128 - 1) = 2 ^ 64 - 1 := by decide
example : high64 (2 ^ 128 - 1) = 2 ^ 64 - 1 := by decide
example : packRotl64_1 0 = 0 := by decide
example : packRotl64_1 1 = 2 := by decide
example : packRotl64_1 (2 ^ 63) = 1 := by decide
example : packRotl64_1 (2 ^ 64) = 2 ^ 65 := by decide
example : packRotl64_1 (2 ^ 127) = 2 ^ 64 := by decide
example : packRotl64_1 rt1Mask = 1 + 2 ^ 64 := by decide
example : packRotl64_1 (2 ^ 128 - 1) = 2 ^ 128 - 1 := by decide
example : packRotl64_1 (2 ^ 192) = 2 ^ 129 := by decide
example : rt1FieldExpr (2 ^ 63) rt1Mask = 1 := by decide
example : rt1FieldExpr (2 ^ 127) rt1Mask = 2 ^ 64 := by decide
example : rt1FieldExpr (2 ^ 128 - 1) rt1Mask = 2 ^ 128 - 1 := by decide
example : rt1FieldExpr 1 1 = rtFieldExpr 1 1 2 := rt1_eq_rt_pow2 1 1
example (w ia : Nat) : rt1FieldExpr w ia = rtFieldExpr w ia 2 := rt1_eq_rt_pow2 w ia
example (w : Nat) (hw : w < 2 ^ 128) : packRotl64_1 w < 2 ^ 128 :=
  packRotl64_1_lt_u128 hw

example (w : Nat) (hw : w < 2 ^ 128) :
    w &&& rt1Mask = 2 ^ 63 * (low64 w / 2 ^ 63 + 2 ^ 64 * (high64 w / 2 ^ 63)) :=
  land_rt1Mask_eq hw
example (w : Nat) (hw : w < 2 ^ 128) :
    rt1FieldExpr w rt1Mask = packRotl64_1 w := rt1FieldExpr_eq_packRotl64_1 hw
example (w : Nat) (hw : w < 2 ^ 128) :
    rtFieldExpr w rt1Mask 2 = packRotl64_1 w := rtFieldExpr_pow2_eq_packRotl64_1 hw
example : rt1FieldExpr (2 ^ 128) rt1Mask ≠ packRotl64_1 (2 ^ 128) := by decide
example : rt1FieldExpr (2 ^ 63) 0 ≠ packRotl64_1 (2 ^ 63) := by decide
example : rt1FieldExpr (2 ^ 63) rt1Mask ≠ (2 * 2 ^ 63) % 2 ^ 128 := by decide
-- The single-lane scaled identity in the external response omitted a factor 2^63.
example : 2 ^ 63 * rotl64_1 (2 ^ 63) ≠
    2 ^ 64 * 2 ^ 63 - (2 ^ 64 - 1) * ((2 ^ 63) / 2 ^ 63) := by decide

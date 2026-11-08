/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaRt1

/-! Numeric constraints extracted manually from Cairo 2.18.0
build_u128_from_felt252 (commit 8746d71d04ca94bb392206bbfc21bcb257d7930a).
This is not a semantics of CASM, memory, hints, RangeCheck or compiler execution.
All predicates below describe admissible numeric outcomes, not traces or totality. -/

namespace MlDsaU128Conversion

open MlDsaRt1

/-- RangeCheck bound for unsigned 128-bit values. -/
def u128Bound : Nat := 2 ^ 128

/-- Literal max_x in the pinned backend; max_y is zero. -/
def maxHigh : Nat := 10633823966279327296825105735305134080

/-- Exact field boundary used by the backend's canonical-recomposition check. -/
theorem prime_eq_maxHigh_mul_bound_add_one :
    cairoPrime = maxHigh * u128Bound + 1 := by decide

/-- Bounds that make the adjusted range-check expressions non-wrapping. -/
theorem bound_constants : 0 < maxHigh ∧ maxHigh < u128Bound ∧
    2 * u128Bound < cairoPrime := by decide

/-- The field zero-test of x - maxHigh agrees with equality of canonical
range-checked limbs. Natural subtraction is padded by the modulus. -/
theorem high_is_max_iff {x : Nat} (hx : x < u128Bound) :
    (x + cairoPrime - maxHigh) % cairoPrime = 0 ↔ x = maxHigh := by
  dsimp [u128Bound, maxHigh, cairoPrime] at *
  omega

/-- The final Wide range-check cell, interpreted as a canonical field residue.
The two additions mirror le_max_y_fix and lt_max_x_fix in the source. -/
def WideRangeCheck (x y : Nat) : Prop :=
  if x = maxHigh then
    (y + (u128Bound - 1)) % cairoPrime < u128Bound
  else
    (x + (u128Bound - maxHigh)) % cairoPrime < u128Bound

/-- Numeric Wide constraints: canonical input, two range-checked limbs,
field recomposition, adjusted range check, and nonzero high limb. -/
def WideChecks (r x y : Nat) : Prop :=
  r < cairoPrime ∧ x < u128Bound ∧ y < u128Bound ∧
    (x * u128Bound + y) % cairoPrime = r ∧ WideRangeCheck x y ∧ x ≠ 0

/-- Adjusted field-residue checks imply the exact upper-limb cap. -/
theorem wideRangeCheck_iff {x y : Nat} (hx : x < u128Bound)
    (hy : y < u128Bound) :
    WideRangeCheck x y ↔ x < maxHigh ∨ (x = maxHigh ∧ y = 0) := by
  unfold WideRangeCheck
  split <;> dsimp [u128Bound, maxHigh, cairoPrime] at * <;> omega

/-- The modular recomposition is an ordinary equality for admissible Wide limbs. -/
theorem wideChecks_recomposition {r x y : Nat} (h : WideChecks r x y) :
    r = x * u128Bound + y ∧ x * u128Bound + y < cairoPrime := by
  rcases h with ⟨hr, hx, hy, heq, hfix, hn⟩
  have hcap := (wideRangeCheck_iff hx hy).mp hfix
  dsimp [u128Bound, maxHigh, cairoPrime] at *
  omega

/-- Equivalence between raw modular checks and an ordinary, canonically bounded
limb decomposition; the forward direction derives ordinary recomposition. -/
theorem wideChecks_iff {r x y : Nat} : WideChecks r x y ↔
    0 < x ∧ x < u128Bound ∧ y < u128Bound ∧ r = x * u128Bound + y ∧
      (x < maxHigh ∨ (x = maxHigh ∧ y = 0)) := by
  constructor
  · intro h
    have heq := (wideChecks_recomposition h).1
    rcases h with ⟨hr, hx, hy, hm, hf, hn⟩
    exact ⟨by omega, hx, hy, heq, (wideRangeCheck_iff hx hy).mp hf⟩
  · rintro ⟨hn, hx, hy, heq, hcap⟩
    have hr : r < cairoPrime := by
      dsimp [u128Bound, maxHigh, cairoPrime] at *
      omega
    refine ⟨hr, hx, hy, ?_, (wideRangeCheck_iff hx hy).mpr hcap, by omega⟩
    rw [← heq, Nat.mod_eq_of_lt hr]

/-- In particular, nonzero high implies a value at least 2^128 only after
canonical recomposition has been established. -/
theorem wideChecks_ge_bound {r x y : Nat} (h : WideChecks r x y) :
    u128Bound ≤ r := by
  have heq := (wideChecks_recomposition h).1
  rcases h with ⟨hr, hx, hy, hm, hf, hn⟩
  dsimp [u128Bound] at *
  omega

/-- No admissible Wide outcome exists below the unsigned bound. -/
theorem not_wideChecks_of_lt {r x y : Nat} (hr : r < u128Bound) :
    ¬ WideChecks r x y := by
  intro h
  have hb := wideChecks_ge_bound h
  omega

/-- Result constructors model numeric branch outcomes, not VM enum layouts. -/
inductive ConversionResult where
  | narrow (value : Nat)
  | wide (high low : Nat)

/-- Narrow retains the range-checked input; Wide satisfies the numeric checks.
This relation makes no assertion that a real execution reaches either outcome. -/
def ConversionChecks (r : Nat) (out : ConversionResult) : Prop :=
  match out with
  | .narrow v => r < cairoPrime ∧ r < u128Bound ∧ v = r
  | .wide x y => WideChecks r x y

/-- Exactly one numeric outcome is admissible for inputs below the bound. -/
theorem conversionChecks_lt_iff {r : Nat} (hr : r < u128Bound)
    (out : ConversionResult) : ConversionChecks r out ↔ out = .narrow r := by
  cases out with
  | narrow v =>
    simp only [ConversionChecks, ConversionResult.narrow.injEq]
    have hp : r < cairoPrime := by
      dsimp [u128Bound, cairoPrime] at *
      omega
    exact ⟨fun h => h.2.2, fun h => ⟨hp, hr, h⟩⟩
  | wide x y =>
    simp only [ConversionChecks]
    constructor
    · intro h
      exact (not_wideChecks_of_lt hr h).elim
    · intro h
      cases h

/-- Existence is only satisfiability of the numeric relation, not VM termination. -/
theorem narrowChecks_exists {r : Nat} (hr : r < u128Bound) :
    ConversionChecks r (.narrow r) := (conversionChecks_lt_iff hr _).mpr rfl

/-- Composition with the proved rt1 arithmetic: the only admissible numeric
outcome is Narrow of the packed two-lane rotation. -/
theorem rt1_conversionChecks_iff {w : Nat} (hw : w < 2 ^ 128)
    (out : ConversionResult) :
    ConversionChecks (rt1FieldExpr w rt1Mask) out ↔
      out = .narrow (packRotl64_1 w) := by
  rw [rt1FieldExpr_eq_packRotl64_1 hw]
  exact conversionChecks_lt_iff (packRotl64_1_lt_u128 hw) out

/-- Specialized no-Wide result for rt1, with no assumption about hint values. -/
theorem rt1_not_wide {w x y : Nat} (hw : w < 2 ^ 128) :
    ¬ WideChecks (rt1FieldExpr w rt1Mask) x y := by
  apply not_wideChecks_of_lt
  rw [rt1FieldExpr_eq_packRotl64_1 hw]
  exact packRotl64_1_lt_u128 hw

/-- Outcome-level Option view; this does not model panic or the Cairo runtime. -/
def resultOption : ConversionResult → Option Nat
  | .narrow v => some v
  | .wide _ _ => none

/-- Successful Option result conditional on the numeric conversion relation. -/
theorem rt1_resultOption_eq_some {w : Nat} (hw : w < 2 ^ 128)
    {out : ConversionResult} (h : ConversionChecks (rt1FieldExpr w rt1Mask) out) :
    resultOption out = some (packRotl64_1 w) := by
  rw [(rt1_conversionChecks_iff hw out).mp h]
  rfl

/-- The original rt model at pow=2 has the same admissible numeric outcome. -/
theorem rt_pow2_conversionChecks_iff {w : Nat} (hw : w < 2 ^ 128)
    (out : ConversionResult) :
    ConversionChecks (rtFieldExpr w rt1Mask 2) out ↔
      out = .narrow (packRotl64_1 w) := by
  rw [← rt1_eq_rt_pow2 w rt1Mask]
  exact rt1_conversionChecks_iff hw out

end MlDsaU128Conversion

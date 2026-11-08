/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaU128Conversion

/-! A pinned production conversion block at PCs 1274..1296.
Literal field decoding is checked below. The extraction from the JSON artifact
and interpretation of instructions as the following assertion relation are manual
trust boundaries, not a verified Cairo VM semantics. Successful numeric exits
are modeled; reachability, caller attribution, hints and termination are not. -/

namespace MlDsaProductionConversionBlock

open MlDsaRt1 MlDsaU128Conversion

/-- Exact 23 field words from Stage15 production CASM SHA-256 4b817187... -/
def blockWords : List Nat := [0xa0680017fff8000, 0x16, 0x480280007ffb8003, 0x480280017ffb8003, 0x4844800180017ffe, 0x100000000000000000000000000000000, 0x483080017ffd7ffb, 0x482480017fff7ffd, 0x800000000000010fffffffffffffffff7ffffffffffffef0000000000000001, 0x20680017fff7ffc, 0x6, 0x402480017fff7ffd, 0xffffffffffffffffffffffffffffffff, 0x10780017fff7fff, 0x4, 0x402480017ffe7ffd, 0xf7ffffffffffffef0000000000000000, 0x400280027ffb7ffd, 0x20680017fff7ffe, 0x11, 0x402780017fff7fff, 0x1, 0x400280007ffb7ffe]

/-- Instruction-start offsets relative to PC1274; immediate words are skipped. -/
def instructionOffsets : List Nat := [0, 2, 3, 4, 6, 7, 9, 11, 13, 15, 17, 18, 20, 22]

/-- Unsigned encoded fields: flags and three biased 16-bit offsets. -/
def decodeFields (word : Nat) : Nat × Nat × Nat × Nat :=
  (word / 2 ^ 48, word % 2 ^ 16, (word / 2 ^ 16) % 2 ^ 16,
    (word / 2 ^ 32) % 2 ^ 16)

/-- Expected fields extracted from the pinned words; not opcode execution rules. -/
def expectedFields : List (Nat × Nat × Nat × Nat) := [
    (2566, 32768, 32767, 32769),
    (18434, 32771, 32763, 32768),
    (18434, 32771, 32763, 32769),
    (18500, 32766, 32769, 32769),
    (18480, 32763, 32765, 32769),
    (18468, 32765, 32767, 32769),
    (518, 32764, 32767, 32769),
    (16420, 32765, 32767, 32769),
    (263, 32767, 32767, 32769),
    (16420, 32765, 32766, 32769),
    (16386, 32765, 32763, 32770),
    (518, 32766, 32767, 32769),
    (16423, 32767, 32767, 32769),
    (16386, 32766, 32763, 32768)]

/-- Kernel-checked correspondence of all 14 instruction words to encoded fields. -/
theorem decoded_fields_exact :
    instructionOffsets.map (fun n => decodeFields (blockWords[n]!)) = expectedFields := by
  decide

/-- Exact finite size of this block, including its immediate words. -/
theorem block_sizes : blockWords.length = 23 ∧ instructionOffsets.length = 14 := by decide

/-- Key immediate values, including the negative high-limb constant as a field residue. -/
theorem immediate_words_exact :
    [blockWords[1]!, blockWords[5]!, blockWords[8]!, blockWords[10]!,
      blockWords[12]!, blockWords[14]!, blockWords[16]!, blockWords[19]!, blockWords[21]!] =
    [22, u128Bound, cairoPrime - maxHigh, 6, u128Bound - 1, 4,
      u128Bound - maxHigh, 17, 1] := by decide

/-- Relative jumps lead to the documented internal and external PCs. -/
theorem relative_targets_exact :
    [1274 + blockWords[1]!, 1283 + blockWords[10]!,
      1287 + blockWords[14]!, 1292 + blockWords[19]!] =
    [1296, 1289, 1291, 1309] := by decide

/-- Named scalar cells in the entry-AP frame, after substituting field assertions.
input=AP-1; selector=AP; shifted=AP+1; difference=AP+2;
checked=AP+3; high=AP+4; low=AP+5. These are not a VM memory model. -/
structure BlockCells where
  input : Nat
  selector : Nat
  shifted : Nat
  difference : Nat
  checked : Nat
  high : Nat
  low : Nat

/-- Numeric assertions along a successful Wide exit at PC1309.
The selector must be zero to enter this path. No correctness of hints is assumed. -/
def WideAssertions (s : BlockCells) : Prop :=
  s.selector = 0 ∧ s.input < cairoPrime ∧ s.high < u128Bound ∧ s.low < u128Bound ∧
  s.shifted = (s.high * u128Bound) % cairoPrime ∧
  s.input = (s.shifted + s.low) % cairoPrime ∧
  s.difference = (s.high + (cairoPrime - maxHigh)) % cairoPrime ∧
  s.checked = (if s.difference = 0 then (s.low + (u128Bound - 1)) % cairoPrime
    else (s.high + (u128Bound - maxHigh)) % cairoPrime) ∧
  s.checked < u128Bound ∧ s.high ≠ 0

/-- Numeric assertions and output bindings of the two successful exits.
AP progression, field/builtin semantics and extraction of this relation from
instructions remain explicit external obligations. -/
def ExitAssertions (s : BlockCells) (out : ConversionResult) : Prop :=
  match out with
  | .narrow v => s.input < cairoPrime ∧ s.selector ≠ 0 ∧ s.input < u128Bound ∧ v = s.input
  | .wide x y => WideAssertions s ∧ x = s.high ∧ y = s.low

/-- The explicit intermediate-cell equations imply the earlier Wide numeric checks. -/
theorem wideAssertions_to_checks {s : BlockCells} (h : WideAssertions s) :
    WideChecks s.input s.high s.low := by
  rcases h with ⟨hs, hr, hx, hy, hp, hv, hd, hf, hb, hn⟩
  have hz : s.difference = 0 ↔ s.high = maxHigh := by
    dsimp [u128Bound, maxHigh, cairoPrime] at *
    omega
  refine ⟨hr, hx, hy, ?_, ?_, hn⟩
  · dsimp [u128Bound, cairoPrime] at *
    omega
  · unfold WideRangeCheck
    by_cases he : s.high = maxHigh
    · have hz0 := hz.mpr he
      rw [if_pos he, if_pos hz0] at *
      omega
    · have hzn : s.difference ≠ 0 := fun h0 => he (hz.mp h0)
      rw [if_neg he, if_neg hzn] at *
      omega

/-- Any successful exit satisfying the extracted assertions meets ConversionChecks. -/
theorem exitAssertions_to_checks {s : BlockCells} {out : ConversionResult}
    (h : ExitAssertions s out) : ConversionChecks s.input out := by
  cases out with
  | narrow v =>
    rcases h with ⟨hr, hs, hb, hv⟩
    exact ⟨hr, hb, hv⟩
  | wide x y =>
    rcases h with ⟨hw, rfl, rfl⟩
    exact wideAssertions_to_checks hw

/-- The failure assertion at PC1294 cannot hold for a canonical field cell. -/
theorem failure_assert_impossible {v : Nat} (_hv : v < cairoPrime) :
    v ≠ (v + 1) % cairoPrime := by
  dsimp [cairoPrime] at *
  omega

/-- No successful extracted Wide path is possible below the unsigned bound. -/
theorem no_wide_assertions_of_lt {s : BlockCells} (hr : s.input < u128Bound) :
    ¬ WideAssertions s := by
  intro h
  exact not_wideChecks_of_lt hr (wideAssertions_to_checks h)

/-- Conditional arithmetic composition, without asserting this block is an rt1 caller. -/
theorem rt1_exit_is_narrow {w : Nat} (hw : w < 2 ^ 128) {s : BlockCells}
    (hin : s.input = rt1FieldExpr w rt1Mask) {out : ConversionResult}
    (h : ExitAssertions s out) : out = .narrow (packRotl64_1 w) := by
  have hc := exitAssertions_to_checks h
  rw [hin] at hc
  exact (rt1_conversionChecks_iff hw out).mp hc

/-- The numeric Option view is Some, conditional on the same input/exit premises. -/
theorem rt1_exit_option {w : Nat} (hw : w < 2 ^ 128) {s : BlockCells}
    (hin : s.input = rt1FieldExpr w rt1Mask) {out : ConversionResult}
    (h : ExitAssertions s out) : resultOption out = some (packRotl64_1 w) := by
  rw [rt1_exit_is_narrow hw hin h]
  rfl

end MlDsaProductionConversionBlock

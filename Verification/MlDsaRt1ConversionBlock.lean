/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaCasmBlockSemantics

/-! Pinned Stage18 candidate conversion at PC3641..3663. This module applies the
existing independent decoded-instruction rules to NEW words and operand addresses.
Three explicit finite paths yield ConversionChecks; arbitrary-trace completeness
and execution after external Wide target6509 are not asserted. The input equation
with rt1 is a conditional premise, not a proved caller/Bitwise/runtime attribution.
Memory is an immutable completed witness; no correctness of hints is assumed. -/

namespace MlDsaRt1ConversionBlock

open MlDsaRt1 MlDsaU128Conversion MlDsaProductionConversionBlock
open MlDsaCasmBlockSemantics

set_option maxRecDepth 4096

/-- Exact new words, externally bound to production CASM SHA256 4b817187... . -/
def candidateWords : List Nat := [
  0xa0680017fff8000,
  0x16,
  0x480080017fe78003,
  0x480080027fe68003,
  0x4844800180017ffe,
  0x100000000000000000000000000000000,
  0x483080017ffd7ff8,
  0x482480017fff7ffd,
  0x800000000000010fffffffffffffffff7ffffffffffffef0000000000000001,
  0x20680017fff7ffc,
  0x6,
  0x402480017fff7ffd,
  0xffffffffffffffffffffffffffffffff,
  0x10780017fff7fff,
  0x4,
  0x402480017ffe7ffd,
  0xf7ffffffffffffef0000000000000000,
  0x400080037fe27ffd,
  0x20680017fff7ffe,
  0xb22,
  0x402780017fff7fff,
  0x1,
  0x400080017fe77ffb]

theorem candidate_sizes : candidateWords.length = 23 ∧ instructionOffsets.length = 14 := by
  decide

theorem relative_targets_exact :
    [3641 + candidateWords[1]!, 3650 + candidateWords[10]!,
      3654 + candidateWords[14]!, 3659 + candidateWords[19]!] =
    [3663, 3656, 3658, 6509] := by decide

/-- A new local fetch window. Exit6509 is outside this model, not a VM halt. -/
def fetch (pc : Nat) : Option Decoded :=
  if 3641 ≤ pc ∧ pc - 3641 ∈ instructionOffsets then
    let word := candidateWords[pc - 3641]!
    if Supported word then some (decode word (candidateWords[pc - 3641 + 1]!)) else none
  else none

def Step (m : Memory) (s t : State) : Prop :=
  match fetch s.pc with
  | some d => DecodedStep m d s t
  | none => False

theorem fetch_3641 : fetch 3641 = some
    ⟨0, 1, 0, -1, 1, 1, 0, 4, 2, 0, 2, 22⟩ := by decide

theorem fetch_3643 : fetch 3643 = some
    ⟨0, 0, 3, -25, 1, 0, 0, 0, 2, 4, 1, 5188287518954913795⟩ := by decide

theorem fetch_3644 : fetch 3644 = some
    ⟨0, 0, 3, -26, 2, 0, 0, 0, 2, 4, 1, 5207427813078040574⟩ := by decide

theorem fetch_3645 : fetch 3645 = some
    ⟨0, 0, -2, 1, 1, 1, 2, 0, 2, 4, 2, u128Bound⟩ := by decide

theorem fetch_3647 : fetch 3647 = some
    ⟨0, 0, -8, -3, 1, 4, 1, 0, 2, 4, 1, 5198420613823168509⟩ := by decide

theorem fetch_3648 : fetch 3648 = some
    ⟨0, 0, -3, -1, 1, 1, 1, 0, 2, 4, 2, cairoPrime - maxHigh⟩ := by decide

theorem fetch_3650 : fetch 3650 = some
    ⟨0, 1, -4, -1, 1, 1, 0, 4, 0, 0, 2, 6⟩ := by decide

theorem fetch_3652 : fetch 3652 = some
    ⟨0, 0, -3, -1, 1, 1, 1, 0, 0, 4, 2, u128Bound - 1⟩ := by decide

theorem fetch_3654 : fetch 3654 = some
    ⟨1, 1, -1, -1, 1, 1, 0, 2, 0, 0, 2, 4⟩ := by decide

theorem fetch_3656 : fetch 3656 = some
    ⟨0, 0, -3, -2, 1, 1, 1, 0, 0, 4, 2, u128Bound - maxHigh⟩ := by decide

theorem fetch_3658 : fetch 3658 = some
    ⟨0, 0, -3, -30, 3, 0, 0, 0, 0, 4, 1, 145944781866893310⟩ := by decide

theorem fetch_3659 : fetch 3659 = some
    ⟨0, 1, -2, -1, 1, 1, 0, 4, 0, 0, 2, 2850⟩ := by decide

theorem fetch_3661 : fetch 3661 = some
    ⟨1, 1, -1, -1, 1, 1, 1, 0, 0, 4, 2, 1⟩ := by decide

theorem fetch_3663 : fetch 3663 = some
    ⟨0, 0, -5, -25, 1, 0, 0, 0, 0, 4, 1, 0⟩ := by decide

/-- A finite trace checks every adjacent pair under the generic instruction rules. -/
def CheckedTrace (m : Memory) : List State → Prop
  | s :: t :: rest => Step m s t ∧ CheckedTrace m (t :: rest)
  | _ => True

/-- Cells selected from immutable memory relative to the block entry AP. -/
def cells (m : Memory) (a : Int) : BlockCells :=
  ⟨m (a + -4), m a, m (a + 1), m (a + 2), m (a + 3), m (a + 4), m (a + 5)⟩

def rcCell (m : Memory) (a : Int) (i : Int) : Nat := m ((m (a + -24) : Int) + (1 + i))

def RangeChecked (m : Memory) (a : Int) (count : Nat) : Prop :=
  ∀ i : Nat, i < count → rcCell m a (i : Int) < u128Bound

/-! Each step lemma uses the closed fetch theorem, then reasons only about symbolic memory. -/

theorem step_entry_narrow (m : Memory) (a f : Int) :
    Step m (frame a f 3641 0) (frame a f 3663 1) ↔
      m a ≠ 0 := by
  by_cases hz : m a = 0 <;>
    simp [Step, frame, fetch_3641, DecodedStep, decodedDst, decodedResult, decodedOp1, base, hz]

theorem step_entry_wide (m : Memory) (a f : Int) :
    Step m (frame a f 3641 0) (frame a f 3643 1) ↔
      m a = 0 := by
  by_cases hz : m a = 0 <;>
    simp [Step, frame, fetch_3641, DecodedStep, decodedDst, decodedResult, decodedOp1, base, hz]

theorem step_high_read (m : Memory) (a f : Int) :
    Step m (frame a f 3643 1) (frame a f 3644 2) ↔
      m (a + 4) = rcCell m a 0 := by
  simp [Step, frame, fetch_3643, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

theorem step_low_read (m : Memory) (a f : Int) :
    Step m (frame a f 3644 2) (frame a f 3645 3) ↔
      m (a + 5) = rcCell m a 1 := by
  simp [Step, frame, fetch_3644, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

theorem step_shift (m : Memory) (a f : Int) :
    Step m (frame a f 3645 3) (frame a f 3647 4) ↔
      m (a + 1) = (m (a + 4) * u128Bound) % cairoPrime := by
  simp [Step, frame, fetch_3645, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_recompose (m : Memory) (a f : Int) :
    Step m (frame a f 3647 4) (frame a f 3648 5) ↔
      m (a + -4) = (m (a + 1) + m (a + 5)) % cairoPrime := by
  simp [Step, frame, fetch_3647, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_difference (m : Memory) (a f : Int) :
    Step m (frame a f 3648 5) (frame a f 3650 6) ↔
      m (a + 2) = (m (a + 4) + (cairoPrime - maxHigh)) % cairoPrime := by
  simp [Step, frame, fetch_3648, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_equal_branch (m : Memory) (a f : Int) :
    Step m (frame a f 3650 6) (frame a f 3652 6) ↔
      m (a + 2) = 0 := by
  by_cases hz : m (a + 2) = 0 <;>
    simp [Step, frame, fetch_3650, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_less_branch (m : Memory) (a f : Int) :
    Step m (frame a f 3650 6) (frame a f 3656 6) ↔
      m (a + 2) ≠ 0 := by
  by_cases hz : m (a + 2) = 0 <;>
    simp [Step, frame, fetch_3650, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_equal_adjust (m : Memory) (a f : Int) :
    Step m (frame a f 3652 6) (frame a f 3654 6) ↔
      m (a + 3) = (m (a + 5) + (u128Bound - 1)) % cairoPrime := by
  simp [Step, frame, fetch_3652, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_equal_jump (m : Memory) (a f : Int) :
    Step m (frame a f 3654 6) (frame a f 3658 6) ↔
      True := by
  simp [Step, frame, fetch_3654, DecodedStep, decodedDst, decodedResult, decodedOp1, base]

theorem step_less_adjust (m : Memory) (a f : Int) :
    Step m (frame a f 3656 6) (frame a f 3658 6) ↔
      m (a + 3) = (m (a + 4) + (u128Bound - maxHigh)) % cairoPrime := by
  simp [Step, frame, fetch_3656, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_adjust_read (m : Memory) (a f : Int) :
    Step m (frame a f 3658 6) (frame a f 3659 6) ↔
      m (a + 3) = rcCell m a 2 := by
  simp [Step, frame, fetch_3658, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

theorem step_wide_exit (m : Memory) (a f : Int) :
    Step m (frame a f 3659 6) (frame a f 6509 6) ↔
      m (a + 4) ≠ 0 := by
  by_cases hz : m (a + 4) = 0 <;>
    simp [Step, frame, fetch_3659, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_failure_branch (m : Memory) (a f : Int) :
    Step m (frame a f 3659 6) (frame a f 3661 6) ↔
      m (a + 4) = 0 := by
  by_cases hz : m (a + 4) = 0 <;>
    simp [Step, frame, fetch_3659, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_failure_assert (m : Memory) (a f : Int) :
    Step m (frame a f 3661 6) (frame a f 3663 6) ↔
      m (f + -1) = (m (f + -1) + 1) % cairoPrime := by
  simp [Step, frame, fetch_3661, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base]

theorem step_narrow_read (m : Memory) (a f : Int) :
    Step m (frame a f 3663 1) (frame a f 3664 1) ↔
      m (a + -4) = rcCell m a 0 := by
  simp [Step, frame, fetch_3663, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

attribute [local irreducible] Step

/-- Narrow path: one branch and one RangeCheck read. -/
def narrowTrace (a f : Int) : List State :=
  [frame a f 3641 0, frame a f 3663 1, frame a f 3664 1]

/-- Common Wide prefix, ending at the high-cap comparison. -/
def widePrefix (a f : Int) : List State :=
  [frame a f 3641 0, frame a f 3643 1, frame a f 3644 2,
   frame a f 3645 3, frame a f 3647 4, frame a f 3648 5, frame a f 3650 6]

/-- Equality branch of the high-cap comparison. -/
def wideEqualTail (a f : Int) : List State :=
  [frame a f 3650 6, frame a f 3652 6, frame a f 3654 6,
   frame a f 3658 6, frame a f 3659 6, frame a f 6509 6]

/-- Nonzero branch of the high-cap comparison. -/
def wideLessTail (a f : Int) : List State :=
  [frame a f 3650 6, frame a f 3656 6,
   frame a f 3658 6, frame a f 3659 6, frame a f 6509 6]

/-- Finite-path boundary witness, including the external Wide exit.
The three paths consist only of generic
instruction steps; output bindings read memory at their documented locations.
This definition does not assume ExitAssertions or any limb-recomposition result.
Completeness for arbitrary external VM traces is not asserted. -/
def BlockExecution (m : Memory) (a f : Int) (out : ConversionResult) : Prop :=
  (CheckedTrace m (narrowTrace a f) ∧ RangeChecked m a 1 ∧
    out = .narrow (m (a + -4))) ∨
  (CheckedTrace m (widePrefix a f) ∧
    (CheckedTrace m (wideEqualTail a f) ∨ CheckedTrace m (wideLessTail a f)) ∧
    RangeChecked m a 3 ∧ out = .wide (m (a + 4)) (m (a + 5)))

/-- A checked Narrow trace yields its numeric exit relation. -/
theorem narrow_trace_to_assertions {m : Memory} {a f : Int} (hc : Canonical m)
    (ht : CheckedTrace m (narrowTrace a f)) (hrc : RangeChecked m a 1) :
    ExitAssertions (cells m a) (.narrow (m (a + -4))) := by
  rcases ht with ⟨h0, h1, _⟩
  have hs := (step_entry_narrow m a f).mp h0
  have hr := (step_narrow_read m a f).mp h1
  have hb := hrc 0 (by decide)
  refine ⟨hc _, hs, ?_, rfl⟩
  change m (a + -4) < u128Bound
  rw [hr]
  exact hb

/-- Prefix and either checked tail imply all intermediate Wide cell assertions. -/
theorem wide_trace_to_assertions {m : Memory} {a f : Int} (hc : Canonical m)
    (hp : CheckedTrace m (widePrefix a f))
    (ht : CheckedTrace m (wideEqualTail a f) ∨ CheckedTrace m (wideLessTail a f))
    (hrc : RangeChecked m a 3) : WideAssertions (cells m a) := by
  rcases hp with ⟨h0, h1, h2, h3, h4, h5, _⟩
  have hs := (step_entry_wide m a f).mp h0
  have hx := (step_high_read m a f).mp h1
  have hy := (step_low_read m a f).mp h2
  have hpv := (step_shift m a f).mp h3
  have hv := (step_recompose m a f).mp h4
  have hd := (step_difference m a f).mp h5
  have hxbound : m (a + 4) < u128Bound := by
    rw [hx]
    exact hrc 0 (by decide)
  have hybound : m (a + 5) < u128Bound := by
    rw [hy]
    exact hrc 1 (by decide)
  rcases ht with he | hl
  · rcases he with ⟨h6, h7, _h8, h9, h10, _⟩
    have hz := (step_equal_branch m a f).mp h6
    have hf := (step_equal_adjust m a f).mp h7
    have hb := (step_adjust_read m a f).mp h9
    have hn := (step_wide_exit m a f).mp h10
    refine ⟨hs, hc _, hxbound, hybound, hpv, hv, hd, ?_, ?_, hn⟩
    · change m (a + 3) = _
      change m (a + 3) = (if m (a + 2) = 0 then _ else _)
      rw [if_pos hz]
      exact hf
    · change m (a + 3) < u128Bound
      rw [hb]
      exact hrc 2 (by decide)
  · rcases hl with ⟨h6, h7, h9, h10, _⟩
    have hz := (step_less_branch m a f).mp h6
    have hf := (step_less_adjust m a f).mp h7
    have hb := (step_adjust_read m a f).mp h9
    have hn := (step_wide_exit m a f).mp h10
    refine ⟨hs, hc _, hxbound, hybound, hpv, hv, hd, ?_, ?_, hn⟩
    · change m (a + 3) = _
      change m (a + 3) = (if m (a + 2) = 0 then _ else _)
      rw [if_neg hz]
      exact hf
    · change m (a + 3) < u128Bound
      rw [hb]
      exact hrc 2 (by decide)

/-- The failing instruction admits no successful step in canonical memory. -/
theorem no_failure_step {m : Memory} {a f : Int} (hc : Canonical m) :
    ¬ Step m (frame a f 3661 6) (frame a f 3663 6) := by
  intro h
  exact failure_assert_impossible (hc _) ((step_failure_assert m a f).mp h)

/-- Main bridge: checked instruction traces and RangeCheck premises yield the
previous numeric relation. No ExitAssertions premise appears in the execution. -/
theorem execution_to_exitAssertions {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (he : BlockExecution m a f out) :
    ExitAssertions (cells m a) out := by
  rcases he with ⟨ht, hr, rfl⟩ | ⟨hp, ht, hr, rfl⟩
  · exact narrow_trace_to_assertions hc ht hr
  · exact ⟨wide_trace_to_assertions hc hp ht hr, rfl, rfl⟩

/-- Composition with the existing conversion theorem. -/
theorem execution_to_conversionChecks {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (he : BlockExecution m a f out) :
    ConversionChecks (m (a + -4)) out :=
  exitAssertions_to_checks (execution_to_exitAssertions hc he)

/-- Conditional rt1 composition; this does not establish the production caller. -/
theorem execution_rt1_narrow {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (he : BlockExecution m a f out) {w : Nat}
    (hw : w < 2 ^ 128) (hin : m (a + -4) = rt1FieldExpr w rt1Mask) :
    out = .narrow (packRotl64_1 w) :=
  rt1_exit_is_narrow hw hin (execution_to_exitAssertions hc he)


/-- Both endpoints are outside the local fetch window; no downstream behavior is modeled. -/
theorem external_fetch_none : fetch 3664 = none ∧ fetch 6509 = none := by decide

theorem wide_paths_end_6509 (a f : Int) :
    (wideEqualTail a f).getLast?.map State.pc = some 6509 ∧
    (wideLessTail a f).getLast?.map State.pc = some 6509 := by
  exact ⟨rfl, rfl⟩

theorem path_lengths (a f : Int) :
    (narrowTrace a f).length = 3 ∧
    (widePrefix a f ++ (wideEqualTail a f).tail).length = 12 ∧
    (widePrefix a f ++ (wideLessTail a f).tail).length = 11 := by
  exact ⟨rfl, rfl, rfl⟩

/-- Under the rt1 input equation, neither checked Wide path can reach its external exit. -/
theorem rt1_no_wide_path {m : Memory} {a f : Int} (hc : Canonical m)
    (hp : CheckedTrace m (widePrefix a f))
    (ht : CheckedTrace m (wideEqualTail a f) ∨ CheckedTrace m (wideLessTail a f))
    (hrc : RangeChecked m a 3) {w : Nat} (hw : w < 2 ^ 128)
    (hin : m (a + -4) = rt1FieldExpr w rt1Mask) : False := by
  have h := wideAssertions_to_checks (wide_trace_to_assertions hc hp ht hrc)
  change WideChecks (m (a + -4)) _ _ at h
  rw [hin] at h
  exact rt1_not_wide hw h

/-- Numeric Option view only: this does not execute unwrap or downstream panic code. -/
theorem execution_rt1_option {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (he : BlockExecution m a f out) {w : Nat}
    (hw : w < 2 ^ 128) (hin : m (a + -4) = rt1FieldExpr w rt1Mask) :
    resultOption out = some (packRotl64_1 w) := by
  rw [execution_rt1_narrow hc he hw hin]
  rfl

/-! Concrete regression witnesses and negative checks for the NEW operand layout. -/
namespace Regression

def narrowMemory (r : Nat) : Memory := fun p =>
  if p = -24 then 100 else if p = 0 then 1 else if p = -4 ∨ p = 101 then r else 0

def wideMemory (h l : Nat) : Memory := fun p =>
  let shifted := (h * u128Bound) % cairoPrime
  let adjusted := (if h = maxHigh then l + (u128Bound - 1)
    else h + (u128Bound - maxHigh)) % cairoPrime
  if p = -24 then 100 else if p = -4 then (shifted + l) % cairoPrime
  else if p = 1 then shifted else if p = 2 then (h + (cairoPrime - maxHigh)) % cairoPrime
  else if p = 3 ∨ p = 103 then adjusted
  else if p = 4 ∨ p = 101 then h else if p = 5 ∨ p = 102 then l else 0

theorem equal_paths :
    CheckedTrace (wideMemory maxHigh 0) (widePrefix 0 200) ∧
    CheckedTrace (wideMemory maxHigh 0) (wideEqualTail 0 200) := by
  constructor <;>
    simp only [widePrefix, wideEqualTail, CheckedTrace, step_entry_wide, step_high_read,
      step_low_read, step_shift, step_recompose, step_difference, step_equal_branch,
      step_equal_adjust, step_equal_jump, step_adjust_read, step_wide_exit] <;>
    norm_num [wideMemory, rcCell, cairoPrime, u128Bound, maxHigh]

theorem less_paths :
    CheckedTrace (wideMemory 1 0) (widePrefix 0 200) ∧
    CheckedTrace (wideMemory 1 0) (wideLessTail 0 200) := by
  constructor <;>
    simp only [widePrefix, wideLessTail, CheckedTrace, step_entry_wide, step_high_read,
      step_low_read, step_shift, step_recompose, step_difference, step_less_branch,
      step_less_adjust, step_adjust_read, step_wide_exit] <;>
    norm_num [wideMemory, rcCell, cairoPrime, u128Bound, maxHigh]

theorem equal_rangeChecks : RangeChecked (wideMemory maxHigh 0) 0 3 := by
  intro i hi
  have hn : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hn with rfl | rfl | rfl <;>
    norm_num [rcCell, wideMemory, cairoPrime, u128Bound, maxHigh]

theorem less_rangeChecks : RangeChecked (wideMemory 1 0) 0 3 := by
  intro i hi
  have hn : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hn with rfl | rfl | rfl <;>
    norm_num [rcCell, wideMemory, cairoPrime, u128Bound, maxHigh]

example : CheckedTrace (narrowMemory 0) (narrowTrace 0 200) := by
  change Step _ _ _ ∧ Step _ _ _ ∧ True
  rw [step_entry_narrow, step_narrow_read]
  decide
example : CheckedTrace (narrowMemory (u128Bound - 1)) (narrowTrace 0 200) := by
  change Step _ _ _ ∧ Step _ _ _ ∧ True
  rw [step_entry_narrow, step_narrow_read]
  decide
example : RangeChecked (narrowMemory (u128Bound - 1)) 0 1 := by
  intro i hi
  have hn : i = 0 := by omega
  subst i
  decide
example : BlockExecution (wideMemory maxHigh 0) 0 200 (.wide maxHigh 0) :=
  Or.inr ⟨equal_paths.1, Or.inl equal_paths.2, equal_rangeChecks, rfl⟩
example : BlockExecution (wideMemory 1 0) 0 200 (.wide 1 0) :=
  Or.inr ⟨less_paths.1, Or.inr less_paths.2, less_rangeChecks, rfl⟩
example : Canonical (wideMemory maxHigh 0) := by
  intro p
  unfold wideMemory
  split_ifs <;> norm_num [cairoPrime, u128Bound, maxHigh]
example : Canonical (wideMemory 1 0) := by
  intro p
  unfold wideMemory
  split_ifs <;> norm_num [cairoPrime, u128Bound, maxHigh]
example : offset candidateWords[22]! 0 = -5 := by decide
example : offset candidateWords[22]! 16 = -25 := by decide
example : offset candidateWords[22]! 32 = 1 := by decide
example : 3659 + candidateWords[19]! = 6509 := by decide
example : fetch 6509 = none := external_fetch_none.2
example : fetch 3664 = none := external_fetch_none.1
example : fetch 1274 = none := by decide
example : fetch 3642 = none := by decide
example : candidateWords[19]! ≠ 17 := by decide
example : offset candidateWords[6]! 0 ≠ -5 := by decide
-- Without the RC premise, a selector claiming Narrow can pass equality assertions.
example : CheckedTrace (narrowMemory u128Bound) (narrowTrace 0 200) := by
  change Step _ _ _ ∧ Step _ _ _ ∧ True
  rw [step_entry_narrow, step_narrow_read]
  decide
example : ¬ RangeChecked (narrowMemory u128Bound) 0 1 := by
  intro h
  have hb := h 0 (by decide)
  change u128Bound < u128Bound at hb
  exact Nat.lt_irrefl _ hb
example : ¬ BlockExecution (narrowMemory 7) 0 200 (.narrow 8) := by
  rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩)
  · simp [narrowMemory] at h
  · cases h
example : ¬ Step (fun _ => 0) (frame 0 200 3659 6) (frame 0 200 6509 6) := by
  rw [step_wide_exit]
  simp
example : ¬ RangeChecked (wideMemory maxHigh 1) 0 3 := by
  intro h
  have hb := h 2 (by decide)
  norm_num [rcCell, wideMemory, cairoPrime, u128Bound, maxHigh] at hb
example : ¬ Step (fun _ => 0) (frame 0 200 3661 6) (frame 0 200 3663 6) := by
  rw [step_failure_assert]
  decide
example : (narrowTrace 0 200).getLast?.map State.pc = some 3664 := rfl
example : (wideEqualTail 0 200).getLast?.map State.pc = some 6509 := rfl
example : (wideLessTail 0 200).getLast?.map State.pc = some 6509 := rfl

end Regression

end MlDsaRt1ConversionBlock

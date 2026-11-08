/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaProductionConversionBlock
import Mathlib.Tactic.NormNum

/-! Stage16: immutable flat-memory semantics for the instruction subset in one
pinned block. Memory is a completed witness, not a hint evaluator or allocator.
Successful paths are explicit finite instruction traces. Correspondence to the
segmented Cairo VM, reachability and callers is open. Stage16c below proves
general finite trace completeness within this model. -/

namespace MlDsaCasmBlockSemantics

set_option maxRecDepth 4096

open MlDsaRt1 MlDsaU128Conversion MlDsaProductionConversionBlock

/-- Flat integer addresses with natural field-cell representatives. -/
abbrev Memory := Int → Nat

/-- All cells in the completed memory witness are canonical field representatives. -/
def Canonical (m : Memory) : Prop := ∀ addr, m addr < cairoPrime

/-- Registers only; memory is immutable throughout a trace. -/
structure State where
  pc : Nat
  ap : Int
  fp : Int
  deriving DecidableEq

/-- Signed offsets are decoded without natural-number truncation. -/
def offset (word shift : Nat) : Int := ((word / 2 ^ shift % 65536 : Nat) : Int) - 32768

def flags (word : Nat) : Nat := word / 2 ^ 48

def base (s : State) (fpFlag : Nat) : Int := if fpFlag = 1 then s.fp else s.ap

def dstValue (m : Memory) (s : State) (word : Nat) : Nat :=
  m (base s (flags word % 2) + offset word 0)

def op0Value (m : Memory) (s : State) (word : Nat) : Nat :=
  m (base s (flags word / 2 % 2) + offset word 16)

/-- Immediate, AP-relative, or indirect-through-op0 addressing. The selected
subset has no FP-relative op1, calls, returns or absolute jumps. -/
def op1Value (m : Memory) (s : State) (word immediate : Nat) : Nat :=
  let mode := flags word / 4 % 8
  if mode = 1 then immediate
  else if mode = 4 then m (s.ap + offset word 32)
  else m ((op0Value m s word : Int) + offset word 32)

def resultValue (m : Memory) (s : State) (word immediate : Nat) : Nat :=
  let mode := flags word / 32 % 4
  if mode = 1 then (op0Value m s word + op1Value m s word immediate) % cairoPrime
  else if mode = 2 then (op0Value m s word * op1Value m s word immediate) % cairoPrime
  else op1Value m s word immediate

def instructionSize (word : Nat) : Nat := if flags word / 4 % 8 = 1 then 2 else 1

/-- Restrict this semantics to the modes actually implemented here. -/
def Supported (word : Nat) : Prop :=
  word < 2 ^ 63 ∧ (flags word / 4 % 8 = 0 ∨ flags word / 4 % 8 = 1 ∨ flags word / 4 % 8 = 4) ∧
  flags word / 32 % 4 ≤ 2 ∧
  (flags word / 128 % 8 = 0 ∨ flags word / 128 % 8 = 2 ∨ flags word / 128 % 8 = 4) ∧
  (flags word / 1024 % 4 = 0 ∨ flags word / 1024 % 4 = 2) ∧
  (flags word / 4096 % 8 = 0 ∨ flags word / 4096 % 8 = 4)

/-- Closed decoding separates bit-field computation from symbolic memory reasoning. -/
structure Decoded where
  dstFP : Nat
  op0FP : Nat
  offDst : Int
  offOp0 : Int
  offOp1 : Int
  op1Mode : Nat
  resMode : Nat
  pcMode : Nat
  apMode : Nat
  opcode : Nat
  size : Nat
  immediate : Nat
  deriving DecidableEq

def decode (word immediate : Nat) : Decoded :=
  ⟨flags word % 2, flags word / 2 % 2, offset word 0, offset word 16,
    offset word 32, flags word / 4 % 8, flags word / 32 % 4,
    flags word / 128 % 8, flags word / 1024 % 4, flags word / 4096 % 8,
    instructionSize word, immediate⟩

instance (word : Nat) : Decidable (Supported word) := by
  unfold Supported
  infer_instance

def decodedDst (m : Memory) (s : State) (d : Decoded) : Nat :=
  m (base s d.dstFP + d.offDst)

def decodedOp0 (m : Memory) (s : State) (d : Decoded) : Nat :=
  m (base s d.op0FP + d.offOp0)

def decodedOp1 (m : Memory) (s : State) (d : Decoded) : Nat :=
  if d.op1Mode = 1 then d.immediate
  else if d.op1Mode = 4 then m (s.ap + d.offOp1)
  else m ((decodedOp0 m s d : Int) + d.offOp1)

def decodedResult (m : Memory) (s : State) (d : Decoded) : Nat :=
  if d.resMode = 1 then (decodedOp0 m s d + decodedOp1 m s d) % cairoPrime
  else if d.resMode = 2 then (decodedOp0 m s d * decodedOp1 m s d) % cairoPrime
  else decodedOp1 m s d

/-- Rules independent of conversion checks, applied to decoded operands.
Memory is a completed immutable witness; no hint correctness is assumed. -/
def DecodedStep (m : Memory) (d : Decoded) (s t : State) : Prop :=
  (d.opcode = 4 → decodedDst m s d = decodedResult m s d) ∧
  t.pc = (if d.pcMode = 4 then
    if decodedDst m s d = 0 then s.pc + d.size else s.pc + decodedOp1 m s d
    else if d.pcMode = 2 then s.pc + decodedResult m s d else s.pc + d.size) ∧
  t.ap = s.ap + (if d.apMode = 2 then 1 else 0) ∧ t.fp = s.fp

def InstructionStep (m : Memory) (word immediate : Nat) (s t : State) : Prop :=
  Supported word ∧ DecodedStep m (decode word immediate) s t

/-- Fetch and decode the exact inherited words; non-instruction addresses fail. -/
def fetch (pc : Nat) : Option Decoded :=
  if 1274 ≤ pc ∧ pc - 1274 ∈ instructionOffsets then
    let word := blockWords[pc - 1274]!
    if Supported word then some (decode word (blockWords[pc - 1274 + 1]!)) else none
  else none

def Step (m : Memory) (s t : State) : Prop :=
  match fetch s.pc with
  | some d => DecodedStep m d s t
  | none => False

theorem fetch_1274 : fetch 1274 = some ⟨0, 1, 0, -1, 1, 1, 0, 4, 2, 0, 2, 22⟩ := by decide

theorem fetch_1276 : fetch 1276 = some
    ⟨0, 1, 3, -5, 0, 0, 0, 0, 2, 4, 1, 5188850464614744067⟩ := by decide

theorem fetch_1277 : fetch 1277 = some
    ⟨0, 1, 3, -5, 1, 0, 0, 0, 2, 4, 1, 5207427813078040574⟩ := by decide

theorem fetch_1278 : fetch 1278 = some ⟨0, 0, -2, 1, 1, 1, 2, 0, 2, 4, 2, u128Bound⟩ := by decide

theorem fetch_1280 : fetch 1280 = some
    ⟨0, 0, -5, -3, 1, 4, 1, 0, 2, 4, 1, 5198420613823168509⟩ := by decide

theorem fetch_1281 : fetch 1281 = some
    ⟨0, 0, -3, -1, 1, 1, 1, 0, 2, 4, 2, cairoPrime - maxHigh⟩ := by decide

theorem fetch_1283 : fetch 1283 = some ⟨0, 1, -4, -1, 1, 1, 0, 4, 0, 0, 2, 6⟩ := by decide

theorem fetch_1285 : fetch 1285 = some
    ⟨0, 0, -3, -1, 1, 1, 1, 0, 0, 4, 2, u128Bound - 1⟩ := by decide

theorem fetch_1287 : fetch 1287 = some ⟨1, 1, -1, -1, 1, 1, 0, 2, 0, 0, 2, 4⟩ := by decide

theorem fetch_1289 : fetch 1289 = some
    ⟨0, 0, -3, -2, 1, 1, 1, 0, 0, 4, 2, u128Bound - maxHigh⟩ := by decide

theorem fetch_1291 : fetch 1291 = some
    ⟨0, 1, -3, -5, 2, 0, 0, 0, 0, 4, 1, 145944781866893310⟩ := by decide

theorem fetch_1292 : fetch 1292 = some ⟨0, 1, -2, -1, 1, 1, 0, 4, 0, 0, 2, 17⟩ := by decide

theorem fetch_1294 : fetch 1294 = some ⟨1, 1, -1, -1, 1, 1, 1, 0, 0, 4, 2, 1⟩ := by decide

theorem fetch_1296 : fetch 1296 = some ⟨0, 1, -2, -5, 0, 0, 0, 0, 0, 4, 1, 0⟩ := by decide

def frame (a f : Int) (pc : Nat) (delta : Int) : State := ⟨pc, a + delta, f⟩

/-- A finite trace checks every adjacent pair under the generic instruction rules. -/
def CheckedTrace (m : Memory) : List State → Prop
  | s :: t :: rest => Step m s t ∧ CheckedTrace m (t :: rest)
  | _ => True

/-- Cells selected from immutable memory relative to the block entry AP. -/
def cells (m : Memory) (a : Int) : BlockCells :=
  ⟨m (a + -1), m a, m (a + 1), m (a + 2), m (a + 3), m (a + 4), m (a + 5)⟩

def rcCell (m : Memory) (f : Int) (i : Int) : Nat := m ((m (f + -5) : Int) + i)

def RangeChecked (m : Memory) (f : Int) (count : Nat) : Prop :=
  ∀ i : Nat, i < count → rcCell m f (i : Int) < u128Bound

/-! Each step lemma uses the closed fetch theorem, then reasons only about symbolic memory. -/

theorem step_entry_narrow (m : Memory) (a f : Int) :
    Step m (frame a f 1274 0) (frame a f 1296 1) ↔
      m a ≠ 0 := by
  by_cases hz : m a = 0 <;>
    simp [Step, frame, fetch_1274, DecodedStep, decodedDst, decodedResult, decodedOp1, base, hz]

theorem step_entry_wide (m : Memory) (a f : Int) :
    Step m (frame a f 1274 0) (frame a f 1276 1) ↔
      m a = 0 := by
  by_cases hz : m a = 0 <;>
    simp [Step, frame, fetch_1274, DecodedStep, decodedDst, decodedResult, decodedOp1, base, hz]

theorem step_high_read (m : Memory) (a f : Int) :
    Step m (frame a f 1276 1) (frame a f 1277 2) ↔
      m (a + 4) = rcCell m f 0 := by
  simp [Step, frame, fetch_1276, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

theorem step_low_read (m : Memory) (a f : Int) :
    Step m (frame a f 1277 2) (frame a f 1278 3) ↔
      m (a + 5) = rcCell m f 1 := by
  simp [Step, frame, fetch_1277, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

theorem step_shift (m : Memory) (a f : Int) :
    Step m (frame a f 1278 3) (frame a f 1280 4) ↔
      m (a + 1) = (m (a + 4) * u128Bound) % cairoPrime := by
  simp [Step, frame, fetch_1278, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_recompose (m : Memory) (a f : Int) :
    Step m (frame a f 1280 4) (frame a f 1281 5) ↔
      m (a + -1) = (m (a + 1) + m (a + 5)) % cairoPrime := by
  simp [Step, frame, fetch_1280, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_difference (m : Memory) (a f : Int) :
    Step m (frame a f 1281 5) (frame a f 1283 6) ↔
      m (a + 2) = (m (a + 4) + (cairoPrime - maxHigh)) % cairoPrime := by
  simp [Step, frame, fetch_1281, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_equal_branch (m : Memory) (a f : Int) :
    Step m (frame a f 1283 6) (frame a f 1285 6) ↔
      m (a + 2) = 0 := by
  by_cases hz : m (a + 2) = 0 <;>
    simp [Step, frame, fetch_1283, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_less_branch (m : Memory) (a f : Int) :
    Step m (frame a f 1283 6) (frame a f 1289 6) ↔
      m (a + 2) ≠ 0 := by
  by_cases hz : m (a + 2) = 0 <;>
    simp [Step, frame, fetch_1283, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_equal_adjust (m : Memory) (a f : Int) :
    Step m (frame a f 1285 6) (frame a f 1287 6) ↔
      m (a + 3) = (m (a + 5) + (u128Bound - 1)) % cairoPrime := by
  simp [Step, frame, fetch_1285, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_equal_jump (m : Memory) (a f : Int) :
    Step m (frame a f 1287 6) (frame a f 1291 6) ↔
      True := by
  simp [Step, frame, fetch_1287, DecodedStep, decodedDst, decodedResult, decodedOp1, base]

theorem step_less_adjust (m : Memory) (a f : Int) :
    Step m (frame a f 1289 6) (frame a f 1291 6) ↔
      m (a + 3) = (m (a + 4) + (u128Bound - maxHigh)) % cairoPrime := by
  simp [Step, frame, fetch_1289, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, add_assoc]

theorem step_adjust_read (m : Memory) (a f : Int) :
    Step m (frame a f 1291 6) (frame a f 1292 6) ↔
      m (a + 3) = rcCell m f 2 := by
  simp [Step, frame, fetch_1291, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

theorem step_wide_exit (m : Memory) (a f : Int) :
    Step m (frame a f 1292 6) (frame a f 1309 6) ↔
      m (a + 4) ≠ 0 := by
  by_cases hz : m (a + 4) = 0 <;>
    simp [Step, frame, fetch_1292, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_failure_branch (m : Memory) (a f : Int) :
    Step m (frame a f 1292 6) (frame a f 1294 6) ↔
      m (a + 4) = 0 := by
  by_cases hz : m (a + 4) = 0 <;>
    simp [Step, frame, fetch_1292, DecodedStep, decodedDst, decodedResult, decodedOp1, base,
      add_assoc, hz]

theorem step_failure_assert (m : Memory) (a f : Int) :
    Step m (frame a f 1294 6) (frame a f 1296 6) ↔
      m (f + -1) = (m (f + -1) + 1) % cairoPrime := by
  simp [Step, frame, fetch_1294, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base]

theorem step_narrow_read (m : Memory) (a f : Int) :
    Step m (frame a f 1296 1) (frame a f 1297 1) ↔
      m (a + -1) = rcCell m f 0 := by
  simp [Step, frame, fetch_1296, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
      base, rcCell, add_assoc]

attribute [local irreducible] Step

/-- Narrow path: one branch and one RangeCheck read. -/
def narrowTrace (a f : Int) : List State :=
  [frame a f 1274 0, frame a f 1296 1, frame a f 1297 1]

/-- Common Wide prefix, ending at the high-cap comparison. -/
def widePrefix (a f : Int) : List State :=
  [frame a f 1274 0, frame a f 1276 1, frame a f 1277 2,
   frame a f 1278 3, frame a f 1280 4, frame a f 1281 5, frame a f 1283 6]

/-- Equality branch of the high-cap comparison. -/
def wideEqualTail (a f : Int) : List State :=
  [frame a f 1283 6, frame a f 1285 6, frame a f 1287 6,
   frame a f 1291 6, frame a f 1292 6, frame a f 1309 6]

/-- Nonzero branch of the high-cap comparison. -/
def wideLessTail (a f : Int) : List State :=
  [frame a f 1283 6, frame a f 1289 6,
   frame a f 1291 6, frame a f 1292 6, frame a f 1309 6]

/-- Successful finite-path witness. The three paths consist only of generic
instruction steps; output bindings read memory at their documented locations.
This definition does not assume ExitAssertions or any limb-recomposition result.
Completeness for arbitrary external VM traces is not asserted. -/
def SuccessfulExecution (m : Memory) (a f : Int) (out : ConversionResult) : Prop :=
  (CheckedTrace m (narrowTrace a f) ∧ RangeChecked m f 1 ∧
    out = .narrow (m (a + -1))) ∨
  (CheckedTrace m (widePrefix a f) ∧
    (CheckedTrace m (wideEqualTail a f) ∨ CheckedTrace m (wideLessTail a f)) ∧
    RangeChecked m f 3 ∧ out = .wide (m (a + 4)) (m (a + 5)))

/-- A successful Narrow trace yields its numeric exit relation. -/
theorem narrow_trace_to_assertions {m : Memory} {a f : Int} (hc : Canonical m)
    (ht : CheckedTrace m (narrowTrace a f)) (hrc : RangeChecked m f 1) :
    ExitAssertions (cells m a) (.narrow (m (a + -1))) := by
  rcases ht with ⟨h0, h1, _⟩
  have hs := (step_entry_narrow m a f).mp h0
  have hr := (step_narrow_read m a f).mp h1
  have hb := hrc 0 (by decide)
  refine ⟨hc _, hs, ?_, rfl⟩
  change m (a + -1) < u128Bound
  rw [hr]
  exact hb

/-- Prefix and either checked tail imply all intermediate Wide cell assertions. -/
theorem wide_trace_to_assertions {m : Memory} {a f : Int} (hc : Canonical m)
    (hp : CheckedTrace m (widePrefix a f))
    (ht : CheckedTrace m (wideEqualTail a f) ∨ CheckedTrace m (wideLessTail a f))
    (hrc : RangeChecked m f 3) : WideAssertions (cells m a) := by
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
    ¬ Step m (frame a f 1294 6) (frame a f 1296 6) := by
  intro h
  exact failure_assert_impossible (hc _) ((step_failure_assert m a f).mp h)

/-- Main bridge: checked instruction traces and RangeCheck premises yield the
previous numeric relation. No ExitAssertions premise appears in the execution. -/
theorem execution_to_exitAssertions {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (he : SuccessfulExecution m a f out) :
    ExitAssertions (cells m a) out := by
  rcases he with ⟨ht, hr, rfl⟩ | ⟨hp, ht, hr, rfl⟩
  · exact narrow_trace_to_assertions hc ht hr
  · exact ⟨wide_trace_to_assertions hc hp ht hr, rfl, rfl⟩

/-- Composition with the existing conversion theorem. -/
theorem execution_to_conversionChecks {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (he : SuccessfulExecution m a f out) :
    ConversionChecks (m (a + -1)) out :=
  exitAssertions_to_checks (execution_to_exitAssertions hc he)

/-- Conditional rt1 composition; this does not establish the production caller. -/
theorem execution_rt1_narrow {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (he : SuccessfulExecution m a f out) {w : Nat}
    (hw : w < 2 ^ 128) (hin : m (a + -1) = rt1FieldExpr w rt1Mask) :
    out = .narrow (packRotl64_1 w) :=
  rt1_exit_is_narrow hw hin (execution_to_exitAssertions hc he)


/-! Focused kernel-checked regression examples; no external VM execution. -/
namespace Regression

def narrowMemory (r : Nat) : Memory := fun addr =>
  if addr = 95 then 10 else if addr = 0 then 1
  else if addr = -1 ∨ addr = 10 then r else 0

example : offset 0x400280007ffb7ffe 0 = -2 := by decide
example : offset 0x400280007ffb7ffe 16 = -5 := by decide
example : offset 0x480280017ffb8003 32 = 1 := by decide
example : flags 0x400280007ffb7ffe / 4096 % 8 = 4 := by decide
example : Supported 0x400280007ffb7ffe := by unfold Supported; decide
example : ¬ Supported (2 ^ 63) := by unfold Supported; decide
example : Step (fun _ => 0) (frame 0 100 1274 0) (frame 0 100 1276 1) := by
  rw [step_entry_wide]
example : ¬ Step (fun _ => 0) (frame 0 100 1274 0) (frame 0 100 1296 1) := by
  rw [step_entry_narrow]
  simp
example : Step (narrowMemory 7) (frame 0 100 1296 1) (frame 0 100 1297 1) := by
  rw [step_narrow_read]
  decide
example : CheckedTrace (narrowMemory 7) (narrowTrace 0 100) := by
  change Step _ _ _ ∧ Step _ _ _ ∧ True
  rw [step_entry_narrow, step_narrow_read]
  decide
example : RangeChecked (narrowMemory 7) 100 1 := by
  intro i hi
  have he : i = 0 := by omega
  subst i
  decide
-- Without the builtin premise the trace itself accepts an out-of-range value.
example : CheckedTrace (narrowMemory u128Bound) (narrowTrace 0 100) := by
  change Step _ _ _ ∧ Step _ _ _ ∧ True
  rw [step_entry_narrow, step_narrow_read]
  decide
example : ¬ RangeChecked (narrowMemory u128Bound) 100 1 := by
  intro h
  have h0 := h 0 (by decide)
  change u128Bound < u128Bound at h0
  exact Nat.lt_irrefl _ h0
-- Wrong output binding cannot be hidden by an otherwise valid trace.
example : ¬ SuccessfulExecution (narrowMemory 7) 0 100 (.narrow 8) := by
  rintro (⟨_, _, he⟩ | ⟨_, _, _, he⟩)
  · simp [narrowMemory] at he
  · cases he
example : ¬ Step (fun _ => 0) (frame 0 100 1292 6) (frame 0 100 1309 6) := by
  rw [step_wide_exit]
  simp
example : Step (fun _ => 0) (frame 0 100 1292 6) (frame 0 100 1294 6) := by
  rw [step_failure_branch]
example : ¬ Step (fun _ => 0) (frame 0 100 1294 6) (frame 0 100 1296 6) := by
  rw [step_failure_assert]
  decide
example : ¬ Step (narrowMemory 7) (frame 0 100 1296 1) (frame 0 100 1298 1) := by
  simp [Step, frame, fetch_1296, DecodedStep]
-- Flip dst offset from -2 to -1: this memory no longer satisfies the read assertion.
example : ¬ InstructionStep (narrowMemory 7) 0x400280007ffb7fff 0
    (frame 0 100 1296 1) (frame 0 100 1297 1) := by
  unfold InstructionStep Supported DecodedStep
  decide
example : ¬ Step (narrowMemory 7) (frame 0 100 1296 1) (frame 0 100 1297 2) := by
  simp [Step, frame, fetch_1296, DecodedStep]

end Regression


/-! Stage16c: arbitrary finite trace classification inside this block model. -/
namespace TraceCompleteness

/-- The next register state, independent of whether the assertion succeeds. -/
def successor (m : Memory) (d : Decoded) (s : State) : State :=
  ⟨if d.pcMode = 4 then
      if decodedDst m s d = 0 then s.pc + d.size else s.pc + decodedOp1 m s d
    else if d.pcMode = 2 then s.pc + decodedResult m s d else s.pc + d.size,
    s.ap + (if d.apMode = 2 then 1 else 0), s.fp⟩

theorem step_successor {m : Memory} {s t : State} {d : Decoded}
    (hf : fetch s.pc = some d) (hs : Step m s t) : t = successor m d s := by
  have h : DecodedStep m d s t := by simpa only [Step, hf] using hs
  rcases t with ⟨pc, ap, fp⟩
  rcases h with ⟨_, hp, ha, hf⟩
  simp only [successor, State.mk.injEq]
  exact ⟨hp, ha, hf⟩

theorem target_1274 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1274 0) t) :
    t = (if m a = 0 then frame a f 1276 1 else frame a f 1296 1) := by
  have h := step_successor (show fetch (frame a f 1274 0).pc = _ from fetch_1274) hs
  by_cases hz : m a = 0 <;>
    simpa [successor, frame, decodedDst, decodedOp1, base, hz] using h

theorem target_1276 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1276 1) t) : t = frame a f 1277 2 := by
  have h := step_successor (show fetch (frame a f 1276 1).pc = _ from fetch_1276) hs
  simpa [successor, frame, add_assoc] using h

theorem target_1277 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1277 2) t) : t = frame a f 1278 3 := by
  have h := step_successor (show fetch (frame a f 1277 2).pc = _ from fetch_1277) hs
  simpa [successor, frame, add_assoc] using h

theorem target_1278 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1278 3) t) : t = frame a f 1280 4 := by
  have h := step_successor (show fetch (frame a f 1278 3).pc = _ from fetch_1278) hs
  simpa [successor, frame, add_assoc] using h

theorem target_1280 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1280 4) t) : t = frame a f 1281 5 := by
  have h := step_successor (show fetch (frame a f 1280 4).pc = _ from fetch_1280) hs
  simpa [successor, frame, add_assoc] using h

theorem target_1281 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1281 5) t) : t = frame a f 1283 6 := by
  have h := step_successor (show fetch (frame a f 1281 5).pc = _ from fetch_1281) hs
  simpa [successor, frame, add_assoc] using h

theorem target_1283 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1283 6) t) :
    t = (if m (a + 2) = 0 then frame a f 1285 6 else frame a f 1289 6) := by
  have h := step_successor (show fetch (frame a f 1283 6).pc = _ from fetch_1283) hs
  by_cases hz : m (a + 2) = 0 <;>
    simpa [successor, frame, decodedDst, decodedOp1, base, hz, add_assoc] using h

theorem target_1285 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1285 6) t) : t = frame a f 1287 6 := by
  have h := step_successor (show fetch (frame a f 1285 6).pc = _ from fetch_1285) hs
  simpa [successor, frame] using h

theorem target_1287 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1287 6) t) : t = frame a f 1291 6 := by
  have h := step_successor (show fetch (frame a f 1287 6).pc = _ from fetch_1287) hs
  simpa [successor, frame, decodedResult, decodedOp1] using h

theorem target_1289 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1289 6) t) : t = frame a f 1291 6 := by
  have h := step_successor (show fetch (frame a f 1289 6).pc = _ from fetch_1289) hs
  simpa [successor, frame] using h

theorem target_1291 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1291 6) t) : t = frame a f 1292 6 := by
  have h := step_successor (show fetch (frame a f 1291 6).pc = _ from fetch_1291) hs
  simpa [successor, frame] using h

theorem target_1292 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1292 6) t) :
    t = (if m (a + 4) = 0 then frame a f 1294 6 else frame a f 1309 6) := by
  have h := step_successor (show fetch (frame a f 1292 6).pc = _ from fetch_1292) hs
  by_cases hz : m (a + 4) = 0 <;>
    simpa [successor, frame, decodedDst, decodedOp1, base, hz, add_assoc] using h

theorem target_1294 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1294 6) t) : t = frame a f 1296 6 := by
  have h := step_successor (show fetch (frame a f 1294 6).pc = _ from fetch_1294) hs
  simpa [successor, frame] using h

theorem target_1296 {m : Memory} {a f : Int} {t : State}
    (hs : Step m (frame a f 1296 1) t) : t = frame a f 1297 1 := by
  have h := step_successor (show fetch (frame a f 1296 1).pc = _ from fetch_1296) hs
  simpa [successor, frame] using h

/-- Final program counter of a nonempty trace is one of the two exits. -/
def EndsAtExit : List State → Prop
  | [] => False
  | [s] => s.pc = 1297 ∨ s.pc = 1309
  | _ :: t :: rest => EndsAtExit (t :: rest)

/-- The endpoint predicate is exactly a condition on the last list element. -/
theorem endsAtExit_iff_getLast (trace : List State) :
    EndsAtExit trace ↔ ∃ s, trace.getLast? = some s ∧ (s.pc = 1297 ∨ s.pc = 1309) := by
  induction trace with
  | nil => simp [EndsAtExit]
  | cons s rest ih =>
    cases rest with
    | nil => simp [EndsAtExit]
    | cons t tail =>
      simpa only [EndsAtExit, List.getLast?_cons_cons] using ih

/-- Peel an arbitrary trace at an internal PC; no bound on its length is used. -/
theorem peel {m : Memory} {s : State} {rest : List State}
    (ht : CheckedTrace m (s :: rest)) (he : EndsAtExit (s :: rest))
    (hn : ¬ (s.pc = 1297 ∨ s.pc = 1309)) :
    ∃ t tail, rest = t :: tail ∧ Step m s t ∧
      CheckedTrace m (t :: tail) ∧ EndsAtExit (t :: tail) := by
  cases rest with
  | nil => exact (hn he).elim
  | cons t tail => exact ⟨t, tail, rfl, ht.1, ht.2, he⟩

theorem fetch_exit_narrow : fetch 1297 = none := by decide

theorem fetch_exit_wide : fetch 1309 = none := by decide

/-- No successor exists after either exit in the restricted block model. -/
theorem no_exit_step {m : Memory} {s t : State}
    (he : s.pc = 1297 ∨ s.pc = 1309) : ¬ Step m s t := by
  rcases he with he | he <;>
    simp only [Step, he, fetch_exit_narrow, fetch_exit_wide, not_false_eq_true]

theorem terminal_tail {m : Memory} {s : State} {rest : List State}
    (ht : CheckedTrace m (s :: rest)) (he : s.pc = 1297 ∨ s.pc = 1309) :
    rest = [] := by
  cases rest with
  | nil => rfl
  | cons t tail => exact (no_exit_step he ht.1).elim

/-- No arbitrary successful trace can start at the failing instruction. -/
theorem no_trace_1294 {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1294 6 :: rest))
    (he : EndsAtExit (frame a f 1294 6 :: rest)) : False := by
  obtain ⟨t, tail, rfl, hs, _, _⟩ := peel ht he (by simp [frame])
  have htarget := target_1294 hs
  subst t
  exact no_failure_step hc hs

theorem finish_1296 {m : Memory} {a f : Int} {rest : List State}
    (ht : CheckedTrace m (frame a f 1296 1 :: rest))
    (he : EndsAtExit (frame a f 1296 1 :: rest)) :
    frame a f 1296 1 :: rest = [frame a f 1296 1, frame a f 1297 1] := by
  obtain ⟨t, tail, rfl, hs, hr, _⟩ := peel ht he (by simp [frame])
  have htarget := target_1296 hs
  subst t
  have hend := terminal_tail hr (by simp [frame])
  subst tail
  rfl

theorem finish_1292 {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1292 6 :: rest))
    (he : EndsAtExit (frame a f 1292 6 :: rest)) :
    frame a f 1292 6 :: rest = [frame a f 1292 6, frame a f 1309 6] := by
  obtain ⟨t, tail, rfl, hs, hr, her⟩ := peel ht he (by simp [frame])
  have htarget := target_1292 hs
  by_cases hz : m (a + 4) = 0
  · rw [if_pos hz] at htarget
    subst t
    exact (no_trace_1294 hc hr her).elim
  · rw [if_neg hz] at htarget
    subst t
    have hend := terminal_tail hr (by simp [frame])
    subst tail
    rfl

theorem finish_1291 {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1291 6 :: rest))
    (he : EndsAtExit (frame a f 1291 6 :: rest)) :
    frame a f 1291 6 :: rest =
      [frame a f 1291 6, frame a f 1292 6, frame a f 1309 6] := by
  obtain ⟨t, tail, rfl, hs, hr, her⟩ := peel ht he (by simp [frame])
  have htarget := target_1291 hs
  subst t
  exact congrArg (List.cons (frame a f 1291 6)) (finish_1292 hc hr her)

theorem finish_1289 {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1289 6 :: rest))
    (he : EndsAtExit (frame a f 1289 6 :: rest)) :
    frame a f 1289 6 :: rest =
      [frame a f 1289 6, frame a f 1291 6, frame a f 1292 6, frame a f 1309 6] := by
  obtain ⟨t, tail, rfl, hs, hr, her⟩ := peel ht he (by simp [frame])
  have htarget := target_1289 hs
  subst t
  exact congrArg (List.cons (frame a f 1289 6)) (finish_1291 hc hr her)

theorem finish_1287 {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1287 6 :: rest))
    (he : EndsAtExit (frame a f 1287 6 :: rest)) :
    frame a f 1287 6 :: rest =
      [frame a f 1287 6, frame a f 1291 6, frame a f 1292 6, frame a f 1309 6] := by
  obtain ⟨t, tail, rfl, hs, hr, her⟩ := peel ht he (by simp [frame])
  have htarget := target_1287 hs
  subst t
  exact congrArg (List.cons (frame a f 1287 6)) (finish_1291 hc hr her)

theorem finish_1285 {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1285 6 :: rest))
    (he : EndsAtExit (frame a f 1285 6 :: rest)) :
    frame a f 1285 6 :: rest =
      [frame a f 1285 6, frame a f 1287 6, frame a f 1291 6,
       frame a f 1292 6, frame a f 1309 6] := by
  obtain ⟨t, tail, rfl, hs, hr, her⟩ := peel ht he (by simp [frame])
  have htarget := target_1285 hs
  subst t
  exact congrArg (List.cons (frame a f 1285 6)) (finish_1287 hc hr her)

theorem finish_1283 {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1283 6 :: rest))
    (he : EndsAtExit (frame a f 1283 6 :: rest)) :
    frame a f 1283 6 :: rest = wideEqualTail a f ∨
    frame a f 1283 6 :: rest = wideLessTail a f := by
  obtain ⟨t, tail, rfl, hs, hr, her⟩ := peel ht he (by simp [frame])
  have htarget := target_1283 hs
  by_cases hz : m (a + 2) = 0
  · rw [if_pos hz] at htarget
    subst t
    exact Or.inl (congrArg (List.cons (frame a f 1283 6)) (finish_1285 hc hr her))
  · rw [if_neg hz] at htarget
    subst t
    exact Or.inr (congrArg (List.cons (frame a f 1283 6)) (finish_1289 hc hr her))

/-- Complete classification from the entry state. The tail is an arbitrary list;
its length is neither bounded nor given as fuel. -/
theorem classify_from_entry {m : Memory} {a f : Int} {rest : List State}
    (hc : Canonical m) (ht : CheckedTrace m (frame a f 1274 0 :: rest))
    (he : EndsAtExit (frame a f 1274 0 :: rest)) :
    frame a f 1274 0 :: rest = narrowTrace a f ∨
    frame a f 1274 0 :: rest = widePrefix a f ++ (wideEqualTail a f).tail ∨
    frame a f 1274 0 :: rest = widePrefix a f ++ (wideLessTail a f).tail := by
  obtain ⟨t, tail, rfl, hs, hr, her⟩ := peel ht he (by simp [frame])
  have htarget := target_1274 hs
  by_cases hz : m a = 0
  · rw [if_pos hz] at htarget
    subst t
    obtain ⟨t0, tail0, rfl, h0, r0, e0⟩ := peel hr her (by simp [frame])
    have q0 := target_1276 h0
    subst t0
    obtain ⟨t1, tail1, rfl, h1, r1, e1⟩ := peel r0 e0 (by simp [frame])
    have q1 := target_1277 h1
    subst t1
    obtain ⟨t2, tail2, rfl, h2, r2, e2⟩ := peel r1 e1 (by simp [frame])
    have q2 := target_1278 h2
    subst t2
    obtain ⟨t3, tail3, rfl, h3, r3, e3⟩ := peel r2 e2 (by simp [frame])
    have q3 := target_1280 h3
    subst t3
    obtain ⟨t4, tail4, rfl, h4, r4, e4⟩ := peel r3 e3 (by simp [frame])
    have q4 := target_1281 h4
    subst t4
    rcases finish_1283 hc r4 e4 with heq | hlt
    · exact Or.inr (Or.inl (congrArg
        (fun xs => frame a f 1274 0 :: frame a f 1276 1 :: frame a f 1277 2 ::
          frame a f 1278 3 :: frame a f 1280 4 :: frame a f 1281 5 :: xs) heq))
    · exact Or.inr (Or.inr (congrArg
        (fun xs => frame a f 1274 0 :: frame a f 1276 1 :: frame a f 1277 2 ::
          frame a f 1278 3 :: frame a f 1280 4 :: frame a f 1281 5 :: xs) hlt))
  · rw [if_neg hz] at htarget
    subst t
    exact Or.inl (congrArg (List.cons (frame a f 1274 0)) (finish_1296 hr her))

/-- User-facing arbitrary-list theorem: start, adjacent Steps and final exit only. -/
theorem trace_classification {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace) :
    trace = narrowTrace a f ∨
    trace = widePrefix a f ++ (wideEqualTail a f).tail ∨
    trace = widePrefix a f ++ (wideLessTail a f).tail := by
  cases trace with
  | nil => simp at hstart
  | cons s rest =>
    have hs : s = frame a f 1274 0 := Option.some.inj hstart
    subst s
    exact classify_from_entry hc ht he

/-- Trace lengths are conclusions: 2, 11 or 10 transitions, respectively. -/
theorem trace_length_classification {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace) :
    trace.length = 3 ∨ trace.length = 12 ∨ trace.length = 11 := by
  rcases trace_classification hc hstart ht he with rfl | rfl | rfl <;>
    simp [narrowTrace, widePrefix, wideEqualTail, wideLessTail]

/-- Read the documented result cells according to the final PC. Only successful
classified traces are used by the theorems below. -/
def traceResult (m : Memory) (a : Int) (trace : List State) : ConversionResult :=
  if trace.getLast?.map State.pc = some 1297 then .narrow (m (a + -1))
  else .wide (m (a + 4)) (m (a + 5))

/-- The builtin premise depends only on the final PC: one or three cells. -/
def TraceRangeChecks (m : Memory) (f : Int) (trace : List State) : Prop :=
  RangeChecked m f (if trace.getLast?.map State.pc = some 1297 then 1 else 3)

theorem split_equal_path {m : Memory} {a f : Int}
    (ht : CheckedTrace m (widePrefix a f ++ (wideEqualTail a f).tail)) :
    CheckedTrace m (widePrefix a f) ∧ CheckedTrace m (wideEqualTail a f) := by
  rcases ht with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, _⟩
  exact ⟨⟨h0, h1, h2, h3, h4, h5, True.intro⟩,
    ⟨h6, h7, h8, h9, h10, True.intro⟩⟩

theorem split_less_path {m : Memory} {a f : Int}
    (ht : CheckedTrace m (widePrefix a f ++ (wideLessTail a f).tail)) :
    CheckedTrace m (widePrefix a f) ∧ CheckedTrace m (wideLessTail a f) := by
  rcases ht with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩
  exact ⟨⟨h0, h1, h2, h3, h4, h5, True.intro⟩,
    ⟨h6, h7, h8, h9, True.intro⟩⟩

/-- Arbitrary traces now construct the earlier explicit-path witness. -/
theorem trace_to_execution {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace)
    (hrc : TraceRangeChecks m f trace) :
    SuccessfulExecution m a f (traceResult m a trace) := by
  rcases trace_classification hc hstart ht he with rfl | rfl | rfl
  · change RangeChecked m f 1 at hrc
    exact Or.inl ⟨ht, hrc, rfl⟩
  · change RangeChecked m f 3 at hrc
    have hp := split_equal_path ht
    exact Or.inr ⟨hp.1, Or.inl hp.2, hrc, rfl⟩
  · change RangeChecked m f 3 at hrc
    have hp := split_less_path ht
    exact Or.inr ⟨hp.1, Or.inr hp.2, hrc, rfl⟩

theorem trace_to_exitAssertions {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace)
    (hrc : TraceRangeChecks m f trace) :
    ExitAssertions (cells m a) (traceResult m a trace) :=
  execution_to_exitAssertions hc (trace_to_execution hc hstart ht he hrc)

theorem trace_to_conversionChecks {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace)
    (hrc : TraceRangeChecks m f trace) :
    ConversionChecks (m (a + -1)) (traceResult m a trace) :=
  exitAssertions_to_checks (trace_to_exitAssertions hc hstart ht he hrc)

theorem trace_rt1_narrow {m : Memory} {a f : Int} {trace : List State}
    (hc : Canonical m) (hstart : trace.head? = some (frame a f 1274 0))
    (ht : CheckedTrace m trace) (he : EndsAtExit trace)
    (hrc : TraceRangeChecks m f trace) {w : Nat} (hw : w < 2 ^ 128)
    (hin : m (a + -1) = rt1FieldExpr w rt1Mask) :
    traceResult m a trace = .narrow (packRotl64_1 w) :=
  rt1_exit_is_narrow hw hin (trace_to_exitAssertions hc hstart ht he hrc)


/-! Regression examples for endpoints, malformed traces, and both Wide paths. -/
namespace Regression16c

example (a f : Int) : EndsAtExit (narrowTrace a f) := by
  simp [EndsAtExit, narrowTrace, frame]

example (a f : Int) :
    EndsAtExit (widePrefix a f ++ (wideEqualTail a f).tail) := by
  simp [EndsAtExit, widePrefix, wideEqualTail, frame]

example (a f : Int) :
    EndsAtExit (widePrefix a f ++ (wideLessTail a f).tail) := by
  simp [EndsAtExit, widePrefix, wideLessTail, frame]

example (a f : Int) : ¬ EndsAtExit [frame a f 1274 0, frame a f 1296 1] := by
  simp [EndsAtExit, frame]

example : ¬ EndsAtExit [] := by simp [EndsAtExit]

example (m : Memory) (a f : Int) (t : State) :
    ¬ CheckedTrace m [frame a f 1297 1, t] := by
  intro h
  exact no_exit_step (by simp [frame]) h.1

example (m : Memory) (a f : Int) (t : State) :
    ¬ CheckedTrace m [frame a f 1309 6, t] := by
  intro h
  exact no_exit_step (by simp [frame]) h.1

example (m : Memory) (a f : Int) :
    ¬ Step m (frame a f 1274 0) (frame a f 1309 6) := by
  intro h
  have ht := target_1274 h
  by_cases hz : m a = 0 <;> simp [hz, frame] at ht

example (m : Memory) (a f : Int) :
    ¬ Step m (frame a f 1274 0) (frame a f 1274 0) := by
  intro h
  have ht := target_1274 h
  by_cases hz : m a = 0 <;> simp [hz, frame] at ht

example {m : Memory} {a f : Int} {trace : List State} (hc : Canonical m)
    (hs : trace.head? = some (frame a f 1274 0)) (ht : CheckedTrace m trace)
    (he : EndsAtExit trace) : trace.length ≠ 13 := by
  have h := trace_length_classification hc hs ht he
  omega

/-- Concrete memory for positive Wide tests, with disjoint stack/RC addresses. -/
def wideMemory (x : Nat) : Memory := fun addr =>
  if addr = 95 then 10
  else if addr = -1 ∨ addr = 1 then (x * u128Bound) % cairoPrime
  else if addr = 2 then (x + (cairoPrime - maxHigh)) % cairoPrime
  else if addr = 3 ∨ addr = 12 then
    if x = maxHigh then u128Bound - 1 else (x + (u128Bound - maxHigh)) % cairoPrime
  else if addr = 4 ∨ addr = 10 then x else 0

example : CheckedTrace (wideMemory maxHigh)
    (widePrefix 0 100 ++ (wideEqualTail 0 100).tail) := by
  simp only [widePrefix, wideEqualTail, List.tail_cons, List.cons_append,
    List.nil_append, CheckedTrace]
  rw [step_entry_wide, step_high_read, step_low_read, step_shift, step_recompose,
    step_difference, step_equal_branch, step_equal_adjust, step_equal_jump,
    step_adjust_read, step_wide_exit]
  decide

example : CheckedTrace (wideMemory 1)
    (widePrefix 0 100 ++ (wideLessTail 0 100).tail) := by
  simp only [widePrefix, wideLessTail, List.tail_cons, List.cons_append,
    List.nil_append, CheckedTrace]
  rw [step_entry_wide, step_high_read, step_low_read, step_shift, step_recompose,
    step_difference, step_less_branch, step_less_adjust, step_adjust_read, step_wide_exit]
  decide

example : RangeChecked (wideMemory maxHigh) 100 3 := by
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide

example : RangeChecked (wideMemory 1) 100 3 := by
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases h with rfl | rfl | rfl <;> decide

example : ¬ CheckedTrace (wideMemory 1)
    (widePrefix 0 100 ++ (wideEqualTail 0 100).tail) := by
  intro h
  have ht := (split_equal_path h).2.1
  have hz := (step_equal_branch (wideMemory 1) 0 100).mp ht
  have hn : wideMemory 1 (0 + 2) ≠ 0 := by decide
  exact hn hz

example (a f : Int) :
    (widePrefix a f ++ (wideEqualTail a f).tail).length = 12 ∧
    (widePrefix a f ++ (wideLessTail a f).tail).length = 11 := by
  simp [widePrefix, wideEqualTail, wideLessTail]

end Regression16c

end TraceCompleteness

end MlDsaCasmBlockSemantics

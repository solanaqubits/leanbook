/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaRt1ConversionBlock

/-! Stage 20: the pinned arithmetic window and its AP bridge to conversion.
The completed flat memory and generic instruction rules are inherited unchanged.
Bitwise semantics is an explicit numeric relation, not runtime pointer provenance.
The input equality required by Stage 19 is derived from instruction checks here.
No arbitrary-trace completeness, runtime reachability or source attribution is asserted. -/

namespace MlDsaRt1ArithmeticBlock

open MlDsaRt1 MlDsaU128Conversion MlDsaCasmBlockSemantics

set_option maxRecDepth 4096

/-- Replicate a 64-bit input into two lanes. -/
def laneFactor : Nat := 1 + 2 ^ 64

/-- Exact production words at PC 3625 through 3640, including three bridge steps. -/
def arithmeticWords : List Nat := [
  0x4846800180198000,
  0x10000000000000001,
  0x480680017fff8000,
  0x80000000000000008000000000000000,
  0x400080057ff17ffe,
  0x400080067ff17fff,
  0x480080077ff18000,
  0x48307ffd7ffd8000,
  0x484480017ffe8000,
  0x100000000000002200000000000000000000000000000002,
  0x48307fff80007ffe,
  0x48468001801a8000,
  0x10000000000000001,
  0x4846800180188000,
  0x10000000000000001,
  0x480080037feb8000]

def arithmeticOffsets : List Nat := [0, 2, 4, 5, 6, 7, 8, 10, 11, 13, 15]

theorem word_sizes : arithmeticWords.length = 16 ∧ arithmeticOffsets.length = 11 := by
  decide

def fetch (pc : Nat) : Option Decoded :=
  if 3625 ≤ pc ∧ pc - 3625 ∈ arithmeticOffsets then
    let word := arithmeticWords[pc - 3625]!
    if Supported word then some (decode word (arithmeticWords[pc - 3625 + 1]!)) else none
  else none

def Step (m : Memory) (s t : State) : Prop :=
  match fetch s.pc with
  | some d => DecodedStep m d s t
  | none => False

def CheckedTrace (m : Memory) : List State → Prop
  | s :: t :: rest => Step m s t ∧ CheckedTrace m (t :: rest)
  | _ => True

theorem fetch_3625 : fetch 3625 = some
    ⟨0, 1, 0, 25, 1, 1, 2, 0, 2, 4, 2, laneFactor⟩ := by decide

theorem fetch_3627 : fetch 3627 = some
    ⟨0, 1, 0, -1, 1, 1, 0, 0, 2, 4, 2, rt1Mask⟩ := by decide

theorem fetch_3629 : fetch 3629 = some
    ⟨0, 0, -2, -15, 5, 0, 0, 0, 0, 4, 1, 4611826783832080383⟩ := by decide

theorem fetch_3630 : fetch 3630 = some
    ⟨0, 0, -1, -15, 6, 0, 0, 0, 0, 4, 1, 5188287540430471168⟩ := by decide

theorem fetch_3631 : fetch 3631 = some
    ⟨0, 0, 0, -15, 7, 0, 0, 0, 2, 4, 1, 5201798296363696128⟩ := by decide

theorem fetch_3632 : fetch 3632 = some
    ⟨0, 0, 0, -3, -3, 4, 1, 0, 2, 4, 1, 5207427813077843968⟩ := by decide

theorem fetch_3633 : fetch 3633 = some
    ⟨0, 0, 0, -2, 1, 1, 2, 0, 2, 4, 2, dConstant⟩ := by decide

theorem fetch_3635 : fetch 3635 = some
    ⟨0, 0, -2, 0, -1, 4, 1, 0, 2, 4, 1, 5207990763033100288⟩ := by decide

theorem fetch_3636 : fetch 3636 = some
    ⟨0, 1, 0, 26, 1, 1, 2, 0, 2, 4, 2, laneFactor⟩ := by decide

theorem fetch_3638 : fetch 3638 = some
    ⟨0, 1, 0, 24, 1, 1, 2, 0, 2, 4, 2, laneFactor⟩ := by decide

theorem fetch_3640 : fetch 3640 = some
    ⟨0, 0, 0, -21, 3, 0, 0, 0, 2, 4, 1, 0⟩ := by decide

theorem step_3625 (m : Memory) (a f : Int) :
    Step m (frame a f 3625 0) (frame a f 3627 1) ↔
      m a = (m (f + 25) * laneFactor) % cairoPrime := by
  simp [Step, frame, fetch_3625, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base]

theorem step_3627 (m : Memory) (a f : Int) :
    Step m (frame a f 3627 1) (frame a f 3629 2) ↔
      m (a + 1) = rt1Mask := by
  simp [Step, frame, fetch_3627, DecodedStep, decodedDst, decodedResult, decodedOp1,
    base, add_assoc]

theorem step_3629 (m : Memory) (a f : Int) :
    Step m (frame a f 3629 2) (frame a f 3630 2) ↔
      m a = m ((m (a + -13) : Int) + 5) := by
  simp [Step, frame, fetch_3629, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3630 (m : Memory) (a f : Int) :
    Step m (frame a f 3630 2) (frame a f 3631 2) ↔
      m (a + 1) = m ((m (a + -13) : Int) + 6) := by
  simp [Step, frame, fetch_3630, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3631 (m : Memory) (a f : Int) :
    Step m (frame a f 3631 2) (frame a f 3632 3) ↔
      m (a + 2) = m ((m (a + -13) : Int) + 7) := by
  simp [Step, frame, fetch_3631, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3632 (m : Memory) (a f : Int) :
    Step m (frame a f 3632 3) (frame a f 3633 4) ↔
      m (a + 3) = (m a + m a) % cairoPrime := by
  simp [Step, frame, fetch_3632, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3633 (m : Memory) (a f : Int) :
    Step m (frame a f 3633 4) (frame a f 3635 5) ↔
      m (a + 4) = (m (a + 2) * dConstant) % cairoPrime := by
  simp [Step, frame, fetch_3633, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3635 (m : Memory) (a f : Int) :
    Step m (frame a f 3635 5) (frame a f 3636 6) ↔
      m (a + 3) = (m (a + 5) + m (a + 4)) % cairoPrime := by
  simp [Step, frame, fetch_3635, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3636 (m : Memory) (a f : Int) :
    Step m (frame a f 3636 6) (frame a f 3638 7) ↔
      m (a + 6) = (m (f + 26) * laneFactor) % cairoPrime := by
  simp [Step, frame, fetch_3636, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3638 (m : Memory) (a f : Int) :
    Step m (frame a f 3638 7) (frame a f 3640 8) ↔
      m (a + 7) = (m (f + 24) * laneFactor) % cairoPrime := by
  simp [Step, frame, fetch_3638, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

theorem step_3640 (m : Memory) (a f : Int) :
    Step m (frame a f 3640 8) (frame a f 3641 9) ↔
      m (a + 8) = m ((m (a + -13) : Int) + 3) := by
  simp [Step, frame, fetch_3640, DecodedStep, decodedDst, decodedResult, decodedOp0, decodedOp1,
    base, add_assoc]

attribute [local irreducible] Step

/-- Full straight-line slice including all AP changes before the conversion. -/
def arithmeticTrace (a f : Int) : List State :=
  [frame a f 3625 0, frame a f 3627 1, frame a f 3629 2, frame a f 3630 2,
   frame a f 3631 2, frame a f 3632 3, frame a f 3633 4, frame a f 3635 5,
   frame a f 3636 6, frame a f 3638 7, frame a f 3640 8, frame a f 3641 9]

/-- Only the local AND buffer equation is assumed. No pointer provenance or
already-computed rt1 result is part of this predicate. -/
def BitwiseAndAt (m : Memory) (b : Int) : Prop :=
  m (b + 7) = (m (b + 5) &&& m (b + 6))

instance (m : Memory) (b : Int) : Decidable (BitwiseAndAt m b) := by
  unfold BitwiseAndAt
  infer_instance

theorem trace_endpoint (a f : Int) :
    (arithmeticTrace a f).getLast? = some (frame (a + 9) f 3641 0) := by
  simp [arithmeticTrace, frame]

theorem input_address (a : Int) : a + 9 + -4 = a + 5 := by omega

/-- Bounds on the source lane imply an exact, nonwrapped 128-bit replication. -/
theorem replicated_bounds {x : Nat} (hx : x < 2 ^ 64) :
    (x * laneFactor) % cairoPrime = x * laneFactor ∧ x * laneFactor < 2 ^ 128 := by
  have hb : x * laneFactor < 2 ^ 128 := by dsimp [laneFactor]; omega
  have hp : 2 ^ 128 < cairoPrime := by decide
  exact ⟨Nat.mod_eq_of_lt (lt_trans hb hp), hb⟩

/-- Instruction assertions at the Bitwise buffer fix the AND result. -/
theorem trace_and {m : Memory} {a f : Int}
    (ht : CheckedTrace m (arithmeticTrace a f))
    (hb : BitwiseAndAt m (m (a + -13) : Int)) :
    m (a + 2) = (m a &&& rt1Mask) := by
  rcases ht with ⟨_, h1, h2, h3, h4, _⟩
  have hm := (step_3627 m a f).mp h1
  have hw := (step_3629 m a f).mp h2
  have hi := (step_3630 m a f).mp h3
  have ho := (step_3631 m a f).mp h4
  unfold BitwiseAndAt at hb
  rw [ho, hb, ← hw, ← hi, hm]

/-- Canonical modular subtraction is determined by its sum assertion.
This handles modular wraparound rather than assuming ordinary subtraction. -/
theorem sum_assertion_to_rt1 {r w : Nat} (hr : r < cairoPrime)
    (hs : (w + w) % cairoPrime =
      (r + ((w &&& rt1Mask) * dConstant) % cairoPrime) % cairoPrime) :
    r = rt1FieldExpr w rt1Mask := by
  unfold rt1FieldExpr
  dsimp [cairoPrime, dConstant] at hr hs ⊢
  omega

/-- The conversion input equation is now a conclusion, not a premise. -/
theorem trace_to_rt1_input {m : Memory} {a f : Int} (hc : Canonical m)
    (ht : CheckedTrace m (arithmeticTrace a f))
    (hb : BitwiseAndAt m (m (a + -13) : Int)) :
    m ((a + 9) + -4) = rt1FieldExpr (m a) rt1Mask := by
  have hand := trace_and ht hb
  rcases ht with ⟨_, _, _, _, _, h5, h6, h7, _⟩
  have hd := (step_3632 m a f).mp h5
  have hm := (step_3633 m a f).mp h6
  have hs := (step_3635 m a f).mp h7
  rw [hand] at hm
  rw [hd, hm] at hs
  rw [input_address]
  exact sum_assertion_to_rt1 (hc _) hs

/-- The actual first instruction supplies the bounded packed word from FP+25. -/
theorem trace_word {m : Memory} {a f : Int}
    (ht : CheckedTrace m (arithmeticTrace a f)) (hx : m (f + 25) < 2 ^ 64) :
    m a = m (f + 25) * laneFactor ∧ m a < 2 ^ 128 := by
  have hw := (step_3625 m a f).mp ht.1
  have hb := replicated_bounds hx
  rw [hb.1] at hw
  exact ⟨hw, hw ▸ hb.2⟩

/-- Arithmetic slice followed by one of the checked conversion paths.
There is no rt1 input equality in the assumptions of this composed theorem. -/
theorem arithmetic_conversion_narrow {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (ht : CheckedTrace m (arithmeticTrace a f))
    (hb : BitwiseAndAt m (m (a + -13) : Int)) (hx : m (f + 25) < 2 ^ 64)
    (he : MlDsaRt1ConversionBlock.BlockExecution m (a + 9) f out) :
    out = .narrow (packRotl64_1 (m a)) := by
  exact MlDsaRt1ConversionBlock.execution_rt1_narrow hc he
    (trace_word ht hx).2 (trace_to_rt1_input hc ht hb)

/-- The externally visible numeric option for the composed local model. -/
theorem arithmetic_conversion_option {m : Memory} {a f : Int} {out : ConversionResult}
    (hc : Canonical m) (ht : CheckedTrace m (arithmeticTrace a f))
    (hb : BitwiseAndAt m (m (a + -13) : Int)) (hx : m (f + 25) < 2 ^ 64)
    (he : MlDsaRt1ConversionBlock.BlockExecution m (a + 9) f out) :
    resultOption out = some (packRotl64_1 (m a)) := by
  rw [arithmetic_conversion_narrow hc ht hb hx he]
  rfl

/-- Neither checked Wide suffix can follow this bounded arithmetic input. -/
theorem arithmetic_no_wide {m : Memory} {a f : Int} (hc : Canonical m)
    (ht : CheckedTrace m (arithmeticTrace a f))
    (hb : BitwiseAndAt m (m (a + -13) : Int)) (hx : m (f + 25) < 2 ^ 64)
    (hp : MlDsaRt1ConversionBlock.CheckedTrace m
      (MlDsaRt1ConversionBlock.widePrefix (a + 9) f))
    (hs : MlDsaRt1ConversionBlock.CheckedTrace m
      (MlDsaRt1ConversionBlock.wideEqualTail (a + 9) f) ∨
      MlDsaRt1ConversionBlock.CheckedTrace m
        (MlDsaRt1ConversionBlock.wideLessTail (a + 9) f))
    (hrc : MlDsaRt1ConversionBlock.RangeChecked m (a + 9) 3) : False := by
  exact MlDsaRt1ConversionBlock.rt1_no_wide_path hc hp hs hrc
    (trace_word ht hx).2 (trace_to_rt1_input hc ht hb)

/-- Input equality stated directly in terms of the original replicated lane. -/
theorem trace_input_replicated {m : Memory} {a f : Int} (hc : Canonical m)
    (ht : CheckedTrace m (arithmeticTrace a f))
    (hb : BitwiseAndAt m (m (a + -13) : Int)) (hx : m (f + 25) < 2 ^ 64) :
    m ((a + 9) + -4) = rt1FieldExpr (m (f + 25) * laneFactor) rt1Mask := by
  rw [trace_to_rt1_input hc ht hb, (trace_word ht hx).1]

/-! Completed numeric witnesses test the instruction assertions, not a runtime
hint solver. Buffers and source cells are distinct in these concrete examples. -/
namespace Regression

def sampleMemory (x : Nat) : Memory := fun p =>
  let w := x * laneFactor
  let t := w &&& rt1Mask
  let r := rt1FieldExpr w rt1Mask
  if p = -13 then 100
  else if p = -15 then 300
  else if p = 225 then x
  else if p = 0 ∨ p = 105 then w
  else if p = 1 ∨ p = 106 then rt1Mask
  else if p = 2 ∨ p = 107 then t
  else if p = 3 then (w + w) % cairoPrime
  else if p = 4 then (t * dConstant) % cairoPrime
  else if p = 5 ∨ p = 301 then r
  else if p = 9 then 1
  else 0

theorem sample_canonical {x : Nat} (hx : x < 2 ^ 64) : Canonical (sampleMemory x) := by
  have hw := (replicated_bounds hx).2
  have hp : 2 ^ 128 < cairoPrime := by decide
  have hxP : x < cairoPrime := lt_trans hx (by decide : 2 ^ 64 < cairoPrime)
  have hwP : x * laneFactor < cairoPrime := lt_trans hw hp
  have htP : (x * laneFactor &&& rt1Mask) < cairoPrime :=
    lt_of_le_of_lt Nat.and_le_left hwP
  intro p
  dsimp [sampleMemory]
  split_ifs <;> first
    | exact hxP
    | exact hwP
    | exact htP
    | exact Nat.mod_lt _ cairoPrime_pos
    | exact Nat.mod_lt _ cairoPrime_pos
    | exact Nat.mod_lt _ cairoPrime_pos
    | decide

theorem sample_trace_zero : CheckedTrace (sampleMemory (0)) (arithmeticTrace 0 200) := by
  simp only [arithmeticTrace, CheckedTrace, step_3625, step_3627, step_3629, step_3630,
    step_3631, step_3632, step_3633, step_3635, step_3636, step_3638, step_3640]
  decide

example : Canonical (sampleMemory (0)) := sample_canonical (by decide)

example : BitwiseAndAt (sampleMemory (0)) 100 := by decide

example : MlDsaRt1ConversionBlock.CheckedTrace (sampleMemory (0))
    (MlDsaRt1ConversionBlock.narrowTrace 9 200) := by
  simp only [MlDsaRt1ConversionBlock.narrowTrace, MlDsaRt1ConversionBlock.CheckedTrace,
    MlDsaRt1ConversionBlock.step_entry_narrow, MlDsaRt1ConversionBlock.step_narrow_read]
  decide

example : MlDsaRt1ConversionBlock.RangeChecked (sampleMemory (0)) 9 1 := by
  intro i hi
  have : i = 0 := by omega
  subst i
  decide

theorem sample_trace_top : CheckedTrace (sampleMemory (2 ^ 63)) (arithmeticTrace 0 200) := by
  simp only [arithmeticTrace, CheckedTrace, step_3625, step_3627, step_3629, step_3630,
    step_3631, step_3632, step_3633, step_3635, step_3636, step_3638, step_3640]
  decide

example : Canonical (sampleMemory (2 ^ 63)) := sample_canonical (by decide)

example : BitwiseAndAt (sampleMemory (2 ^ 63)) 100 := by decide

example : MlDsaRt1ConversionBlock.CheckedTrace (sampleMemory (2 ^ 63))
    (MlDsaRt1ConversionBlock.narrowTrace 9 200) := by
  simp only [MlDsaRt1ConversionBlock.narrowTrace, MlDsaRt1ConversionBlock.CheckedTrace,
    MlDsaRt1ConversionBlock.step_entry_narrow, MlDsaRt1ConversionBlock.step_narrow_read]
  decide

example : MlDsaRt1ConversionBlock.RangeChecked (sampleMemory (2 ^ 63)) 9 1 := by
  intro i hi
  have : i = 0 := by omega
  subst i
  decide

theorem sample_trace_max : CheckedTrace (sampleMemory (2 ^ 64 - 1)) (arithmeticTrace 0 200) := by
  simp only [arithmeticTrace, CheckedTrace, step_3625, step_3627, step_3629, step_3630,
    step_3631, step_3632, step_3633, step_3635, step_3636, step_3638, step_3640]
  decide

example : Canonical (sampleMemory (2 ^ 64 - 1)) := sample_canonical (by decide)

example : BitwiseAndAt (sampleMemory (2 ^ 64 - 1)) 100 := by decide

example : MlDsaRt1ConversionBlock.CheckedTrace (sampleMemory (2 ^ 64 - 1))
    (MlDsaRt1ConversionBlock.narrowTrace 9 200) := by
  simp only [MlDsaRt1ConversionBlock.narrowTrace, MlDsaRt1ConversionBlock.CheckedTrace,
    MlDsaRt1ConversionBlock.step_entry_narrow, MlDsaRt1ConversionBlock.step_narrow_read]
  decide

example : MlDsaRt1ConversionBlock.RangeChecked (sampleMemory (2 ^ 64 - 1)) 9 1 := by
  intro i hi
  have : i = 0 := by omega
  subst i
  decide

/-- A concrete end-to-end witness exercises the composed theorem at a wraparound input. -/
example : MlDsaU128Conversion.ConversionResult.narrow (sampleMemory (2 ^ 63) 5) =
    .narrow (packRotl64_1 (sampleMemory (2 ^ 63) 0)) := by
  apply arithmetic_conversion_narrow (sample_canonical (by decide)) sample_trace_top
  · decide
  · decide
  · left
    refine ⟨?_, ?_, rfl⟩
    · simp only [MlDsaRt1ConversionBlock.narrowTrace, MlDsaRt1ConversionBlock.CheckedTrace,
        MlDsaRt1ConversionBlock.step_entry_narrow, MlDsaRt1ConversionBlock.step_narrow_read]
      decide
    · intro i hi
      have : i = 0 := by omega
      subst i
      decide

-- Wrong AP accounting chooses a different, unrelated materialized cell.
example : sampleMemory (2 ^ 63) (9 + -1) ≠
    rt1FieldExpr (sampleMemory (2 ^ 63) 0) rt1Mask := by decide

-- A corrupted result cell violates the subtraction instruction assertion.
example : ¬ Step (fun p => if p = 5 then 0 else sampleMemory (2 ^ 63) p)
    (frame 0 200 3635 5) (frame 0 200 3636 6) := by
  rw [step_3635]
  decide

-- Replacing the AND slot with an incompatible value breaks the explicit builtin relation.
example : ¬ BitwiseAndAt (fun p => if p = 107 then 0 else sampleMemory (2 ^ 63) p) 100 := by
  decide

example : (2 ^ 64) * laneFactor ≥ 2 ^ 128 := by decide

example : fetch 3626 = none ∧ fetch 3641 = none := by decide

example : (arithmeticTrace 0 200).length = 12 := by decide

example : (9 : Int) + -4 = 5 := by decide

end Regression
end MlDsaRt1ArithmeticBlock

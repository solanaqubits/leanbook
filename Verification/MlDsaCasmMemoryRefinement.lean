/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaCasmBlockSemantics

/-! Forward refinement of an abstract typed segmented memory into the pinned
flat block model. Nat segment identifiers deliberately exclude temporary negative
segments. No concrete Cairo VM revision is identified or verified here. This is
an immutable partial memory witness, not an allocator or an operand-deduction engine.
A common canonical flat realization is an explicit premise, not an existence claim. -/

namespace MlDsaCasmMemoryRefinement

open MlDsaRt1 MlDsaU128Conversion MlDsaProductionConversionBlock MlDsaCasmBlockSemantics

set_option maxRecDepth 4096

structure Relocatable where
  seg : Nat
  off : Nat
  deriving DecidableEq

inductive SegValue where
  | felt (v : Nat)
  | ptr (p : Relocatable)
  deriving DecidableEq

abbrev SegMemory := Relocatable → Option SegValue
abbrev RelocTable := Nat → Int

def relocAddr (ρ : RelocTable) (p : Relocatable) : Int := ρ p.seg + p.off

def relocVal (ρ : RelocTable) : SegValue → Nat
  | .felt v => v
  | .ptr p => (relocAddr ρ p).toNat

def ValidValue (ρ : RelocTable) : SegValue → Prop
  | .felt v => v < cairoPrime
  | .ptr p => 0 ≤ relocAddr ρ p ∧ relocAddr ρ p < (cairoPrime : Int)

/-- Offsets cannot cross the beginning of a segment. Segment sizes are not modeled. -/
def addOffset (p : Relocatable) (d : Int) : Option Relocatable :=
  if 0 ≤ (p.off : Int) + d then some ⟨p.seg, ((p.off : Int) + d).toNat⟩ else none

theorem addOffset_coordinates {p q : Relocatable} {d : Int}
    (h : addOffset p d = some q) : q.seg = p.seg ∧ (q.off : Int) = p.off + d := by
  unfold addOffset at h
  split at h
  · rename_i hn
    have hq := Option.some.inj h
    subst q
    exact ⟨rfl, Int.toNat_of_nonneg hn⟩
  · contradiction

theorem reloc_addOffset {ρ : RelocTable} {p q : Relocatable} {d : Int}
    (h : addOffset p d = some q) : relocAddr ρ q = relocAddr ρ p + d := by
  have hc := addOffset_coordinates h
  unfold relocAddr
  rw [hc.1, hc.2]
  omega

theorem addOffset_nat_off {p q : Relocatable} {n : Nat}
    (h : addOffset p (n : Int) = some q) : q.off = p.off + n := by
  have hc := (addOffset_coordinates h).2
  omega

/-- Every defined cell, including pointer values, agrees with a canonical flat witness. -/
structure RelocatesTo (ρ : RelocTable) (sm : SegMemory) (m : Memory) : Prop where
  canonical : Canonical m
  cells : ∀ p v, sm p = some v →
    ValidValue ρ v ∧ m (relocAddr ρ p) = relocVal ρ v

/-- Optional footprint injectivity. Forward preservation below needs the supplied
realization, not a claim that this condition alone constructs that realization. -/
def NonAliasing (ρ : RelocTable) (sm : SegMemory) : Prop :=
  ∀ p q, sm p ≠ none → sm q ≠ none → relocAddr ρ p = relocAddr ρ q → p = q

/-- An extension may initialize cells but cannot change any prior defined value. -/
def WriteOnceExtension (sm sm' : SegMemory) : Prop :=
  ∀ p v, sm p = some v → sm' p = some v

theorem relocation_restrict {ρ : RelocTable} {sm sm' : SegMemory} {m : Memory}
    (he : WriteOnceExtension sm sm') (hr : RelocatesTo ρ sm' m) :
    RelocatesTo ρ sm m :=
  ⟨hr.canonical, fun p v h => hr.cells p v (he p v h)⟩

theorem write_once_no_conflict {sm sm' : SegMemory} {p : Relocatable} {v w : SegValue}
    (he : WriteOnceExtension sm sm') (hv : sm p = some v) (hw : sm' p = some w) :
    v = w := Option.some.inj ((he p v hv).symm.trans hw)

/-- Typed read through a checked signed offset. -/
def ReadAt (sm : SegMemory) (p : Relocatable) (d : Int) (v : SegValue) : Prop :=
  ∃ q, addOffset p d = some q ∧ sm q = some v

theorem read_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {p : Relocatable} {d : Int} {v : SegValue}
    (h : ReadAt sm p d v) :
    ValidValue ρ v ∧ m (relocAddr ρ p + d) = relocVal ρ v := by
  rcases h with ⟨q, ha, hv⟩
  have hc := hr.cells q v hv
  rw [reloc_addOffset ha] at hc
  exact hc

theorem read_felt_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {p : Relocatable} {d : Int} {v : Nat}
    (h : ReadAt sm p d (.felt v)) : m (relocAddr ρ p + d) = v :=
  (read_projection hr h).2

theorem read_ptr_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {p q : Relocatable} {d : Int}
    (h : ReadAt sm p d (.ptr q)) :
    (m (relocAddr ρ p + d) : Int) = relocAddr ρ q := by
  have hc := read_projection hr h
  rw [hc.2]
  exact Int.toNat_of_nonneg hc.1.1

structure SegState where
  pc : Relocatable
  ap : Relocatable
  fp : Relocatable
  deriving DecidableEq

/-- PC stays a program offset; AP/FP become relocated addresses. Program segment
membership is checked by CodeRead and endpoint conditions, not by this total map. -/
def projectState (ρ : RelocTable) (s : SegState) : State :=
  ⟨s.pc.off, relocAddr ρ s.ap, relocAddr ρ s.fp⟩

def segBase (s : SegState) (flag : Nat) : Relocatable :=
  if flag = 1 then s.fp else s.ap

theorem reloc_segBase (ρ : RelocTable) (s : SegState) (flag : Nat) :
    relocAddr ρ (segBase s flag) = base (projectState ρ s) flag := by
  by_cases h : flag = 1 <;> simp [segBase, base, projectState, h]

/-- Instruction memory really contains the pinned word and, where used, immediate.
The finite decoder is shared with the flat model; no compiler theorem is claimed. -/
structure CodeRead (sm : SegMemory) (prog : Nat) (p : Relocatable) (d : Decoded) : Prop where
  segment : p.seg = prog
  valid : 1274 ≤ p.off ∧ p.off - 1274 ∈ instructionOffsets
  word : sm p = some (.felt (blockWords[p.off - 1274]!))
  supported : Supported (blockWords[p.off - 1274]!)
  decoded : d = decode (blockWords[p.off - 1274]!) (blockWords[p.off - 1274 + 1]!)
  immediate : d.op1Mode = 1 →
    sm ⟨p.seg, p.off + 1⟩ = some (.felt (blockWords[p.off - 1274 + 1]!))

theorem code_read_fetch {sm : SegMemory} {prog : Nat} {p : Relocatable} {d : Decoded}
    (h : CodeRead sm prog p d) : fetch p.off = some d := by
  simp only [fetch, if_pos h.valid, if_pos h.supported]
  rw [h.decoded]

/-- Only used operands are read: unconditional jumps need no dst scalar. -/
def Op1Read (sm : SegMemory) (s : SegState) (d : Decoded) (v : Nat) : Prop :=
  if d.op1Mode = 1 then v = d.immediate
  else if d.op1Mode = 4 then ReadAt sm s.ap d.offOp1 (.felt v)
  else ∃ p, ReadAt sm (segBase s d.op0FP) d.offOp0 (.ptr p) ∧
    ReadAt sm p d.offOp1 (.felt v)

def ResultRead (sm : SegMemory) (s : SegState) (d : Decoded) (v : Nat) : Prop :=
  if d.resMode = 1 then ∃ x y,
    ReadAt sm (segBase s d.op0FP) d.offOp0 (.felt x) ∧ Op1Read sm s d y ∧
    v = (x + y) % cairoPrime
  else if d.resMode = 2 then ∃ x y,
    ReadAt sm (segBase s d.op0FP) d.offOp0 (.felt x) ∧ Op1Read sm s d y ∧
    v = (x * y) % cairoPrime
  else Op1Read sm s d v

theorem op1_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {s : SegState} {d : Decoded} {v : Nat}
    (h : Op1Read sm s d v) : decodedOp1 m (projectState ρ s) d = v := by
  unfold Op1Read at h
  unfold decodedOp1
  by_cases h1 : d.op1Mode = 1
  · rw [if_pos h1] at h ⊢
    exact h.symm
  · rw [if_neg h1] at h ⊢
    by_cases h4 : d.op1Mode = 4
    · rw [if_pos h4] at h ⊢
      exact read_felt_projection hr h
    · rw [if_neg h4] at h ⊢
      rcases h with ⟨p, hp, hv⟩
      have hx := read_ptr_projection hr hp
      rw [reloc_segBase] at hx
      change (decodedOp0 m (projectState ρ s) d : Int) = relocAddr ρ p at hx
      rw [hx]
      exact read_felt_projection hr hv

theorem result_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {s : SegState} {d : Decoded} {v : Nat}
    (h : ResultRead sm s d v) : decodedResult m (projectState ρ s) d = v := by
  unfold ResultRead at h
  unfold decodedResult
  by_cases h1 : d.resMode = 1
  · rw [if_pos h1] at h ⊢
    rcases h with ⟨x, y, hx, hy, hv⟩
    have hx' := read_felt_projection hr hx
    rw [reloc_segBase] at hx'
    change decodedOp0 m (projectState ρ s) d = x at hx'
    rw [hx', op1_projection hr hy]
    exact hv.symm
  · rw [if_neg h1] at h ⊢
    by_cases h2 : d.resMode = 2
    · rw [if_pos h2] at h ⊢
      rcases h with ⟨x, y, hx, hy, hv⟩
      have hx' := read_felt_projection hr hx
      rw [reloc_segBase] at hx'
      change decodedOp0 m (projectState ρ s) d = x at hx'
      rw [hx', op1_projection hr hy]
      exact hv.symm
    · rw [if_neg h2] at h ⊢
      exact op1_projection hr h

def AssertionRead (sm : SegMemory) (s : SegState) (d : Decoded) : Prop :=
  d.opcode = 4 → ∃ v,
    ReadAt sm (segBase s d.dstFP) d.offDst (.felt v) ∧ ResultRead sm s d v

/-- Segmented control flow uses checked address arithmetic, not the flat Step. -/
def ControlRead (sm : SegMemory) (s t : SegState) (d : Decoded) : Prop :=
  if d.pcMode = 4 then ∃ v jump,
    ReadAt sm (segBase s d.dstFP) d.offDst (.felt v) ∧ Op1Read sm s d jump ∧
    addOffset s.pc ((if v = 0 then d.size else jump : Nat) : Int) = some t.pc
  else if d.pcMode = 2 then ∃ jump,
    ResultRead sm s d jump ∧ addOffset s.pc (jump : Int) = some t.pc
  else addOffset s.pc (d.size : Int) = some t.pc

/-- Typed instruction constraints over a common partial memory. Allocation,
deduction of unknown operands and transition-wise memory construction are excluded. -/
def SegStep (sm : SegMemory) (prog : Nat) (s t : SegState) : Prop :=
  ∃ d, CodeRead sm prog s.pc d ∧ AssertionRead sm s d ∧ ControlRead sm s t d ∧
    addOffset s.ap (if d.apMode = 2 then 1 else 0) = some t.ap ∧ t.fp = s.fp

theorem control_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {s t : SegState} {d : Decoded}
    (h : ControlRead sm s t d) :
    (projectState ρ t).pc =
      (if d.pcMode = 4 then
        if decodedDst m (projectState ρ s) d = 0 then (projectState ρ s).pc + d.size
        else (projectState ρ s).pc + decodedOp1 m (projectState ρ s) d
      else if d.pcMode = 2 then
        (projectState ρ s).pc + decodedResult m (projectState ρ s) d
      else (projectState ρ s).pc + d.size) := by
  unfold ControlRead at h
  by_cases h4 : d.pcMode = 4
  · rw [if_pos h4] at h ⊢
    rcases h with ⟨v, jump, hv, hj, ha⟩
    have hv' := read_felt_projection hr hv
    rw [reloc_segBase] at hv'
    change decodedDst m (projectState ρ s) d = v at hv'
    rw [hv', op1_projection hr hj]
    have hp := addOffset_nat_off ha
    by_cases hz : v = 0 <;> simpa [hz, projectState] using hp
  · rw [if_neg h4] at h ⊢
    by_cases h2 : d.pcMode = 2
    · rw [if_pos h2] at h ⊢
      rcases h with ⟨jump, hj, ha⟩
      rw [result_projection hr hj]
      exact addOffset_nat_off ha
    · rw [if_neg h2] at h ⊢
      exact addOffset_nat_off h

/-- Forward instruction preservation. No flat Step occurs in the SegStep premises. -/
theorem step_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {prog : Nat} {s t : SegState}
    (h : SegStep sm prog s t) : Step m (projectState ρ s) (projectState ρ t) := by
  rcases h with ⟨d, hf, ha, hc, hap, hfp⟩
  have hfetch : fetch (projectState ρ s).pc = some d := code_read_fetch hf
  rw [Step, hfetch]
  refine ⟨?_, control_projection hr hc, ?_, ?_⟩
  · intro hop
    rcases ha hop with ⟨v, hv, hres⟩
    have hv' := read_felt_projection hr hv
    rw [reloc_segBase] at hv'
    exact hv'.trans (result_projection hr hres).symm
  · exact reloc_addOffset hap
  · change relocAddr ρ t.fp = relocAddr ρ s.fp
    rw [hfp]

def SegCheckedTrace (sm : SegMemory) (prog : Nat) : List SegState → Prop
  | s :: t :: rest => SegStep sm prog s t ∧ SegCheckedTrace sm prog (t :: rest)
  | _ => True

theorem trace_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) (prog : Nat) (trace : List SegState) :
    SegCheckedTrace sm prog trace → CheckedTrace m (trace.map (projectState ρ)) := by
  induction trace with
  | nil => intro _; trivial
  | cons s rest ih =>
    cases rest with
    | nil => intro _; trivial
    | cons t tail =>
      intro h
      exact ⟨step_projection hr h.1, ih h.2⟩

def SegEndsAtExit (prog : Nat) : List SegState → Prop
  | [] => False
  | [s] => s.pc.seg = prog ∧ (s.pc.off = 1297 ∨ s.pc.off = 1309)
  | _ :: t :: rest => SegEndsAtExit prog (t :: rest)

theorem ends_projection (ρ : RelocTable) (prog : Nat) (trace : List SegState) :
    SegEndsAtExit prog trace → TraceCompleteness.EndsAtExit (trace.map (projectState ρ)) := by
  induction trace with
  | nil => intro h; exact h.elim
  | cons s rest ih =>
    cases rest with
    | nil => intro h; exact h.2
    | cons t tail => intro h; exact ih h

theorem start_projection {ρ : RelocTable} {trace : List SegState} {s : SegState}
    (hs : trace.head? = some s) (hp : s.pc.off = 1274) :
    (trace.map (projectState ρ)).head? =
      some (frame (relocAddr ρ s.ap) (relocAddr ρ s.fp) 1274 0) := by
  cases trace with
  | nil => simp at hs
  | cons t tail =>
    have ht : t = s := Option.some.inj hs
    subst t
    simp [projectState, frame, hp]

/-- Universal classification of the projected list, not an assumption about paths. -/
theorem trace_projection_classification {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {prog : Nat} {trace : List SegState} {s : SegState}
    (hs : trace.head? = some s) (hp : s.pc.seg = prog ∧ s.pc.off = 1274)
    (ht : SegCheckedTrace sm prog trace) (he : SegEndsAtExit prog trace) :
    trace.map (projectState ρ) = narrowTrace (relocAddr ρ s.ap) (relocAddr ρ s.fp) ∨
    trace.map (projectState ρ) = widePrefix (relocAddr ρ s.ap) (relocAddr ρ s.fp) ++
      (wideEqualTail (relocAddr ρ s.ap) (relocAddr ρ s.fp)).tail ∨
    trace.map (projectState ρ) = widePrefix (relocAddr ρ s.ap) (relocAddr ρ s.fp) ++
      (wideLessTail (relocAddr ρ s.ap) (relocAddr ρ s.fp)).tail :=
  TraceCompleteness.trace_classification hr.canonical (start_projection hs hp.2)
    (trace_projection hr prog trace ht) (ends_projection ρ prog trace he)

theorem segmented_trace_lengths {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {prog : Nat} {trace : List SegState} {s : SegState}
    (hs : trace.head? = some s) (hp : s.pc.seg = prog ∧ s.pc.off = 1274)
    (ht : SegCheckedTrace sm prog trace) (he : SegEndsAtExit prog trace) :
    trace.length = 3 ∨ trace.length = 12 ∨ trace.length = 11 := by
  have h := TraceCompleteness.trace_length_classification hr.canonical
    (start_projection hs hp.2) (trace_projection hr prog trace ht)
    (ends_projection ρ prog trace he)
  simpa only [List.length_map] using h

/-- RangeCheck pointer must be a pointer value, and checked cells must be scalars. -/
def SegRangeChecks (sm : SegMemory) (fp : Relocatable) (count : Nat) : Prop :=
  ∃ ptr, ReadAt sm fp (-5) (.ptr ptr) ∧
    ∀ i : Nat, i < count → ∃ v, ReadAt sm ptr (i : Int) (.felt v) ∧ v < u128Bound

theorem rangecheck_projection {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {fp : Relocatable} {count : Nat}
    (h : SegRangeChecks sm fp count) : RangeChecked m (relocAddr ρ fp) count := by
  rcases h with ⟨ptr, hp, hc⟩
  intro i hi
  rcases hc i hi with ⟨v, hv, hb⟩
  have hptr := read_ptr_projection hr hp
  change m ((m (relocAddr ρ fp + -5) : Int) + (i : Int)) < u128Bound
  rw [hptr, read_felt_projection hr hv]
  exact hb

/-- Count selection depends only on the projected endpoint, not on flat memory. -/
def SegTraceRangeChecks (ρ : RelocTable) (sm : SegMemory) (fp : Relocatable)
    (trace : List SegState) : Prop :=
  SegRangeChecks sm fp (if (trace.map (projectState ρ)).getLast?.map State.pc = some 1297
    then 1 else 3)

theorem trace_projection_exitAssertions {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {prog : Nat} {trace : List SegState} {s : SegState}
    (hs : trace.head? = some s) (hp : s.pc.seg = prog ∧ s.pc.off = 1274)
    (ht : SegCheckedTrace sm prog trace) (he : SegEndsAtExit prog trace)
    (hrc : SegTraceRangeChecks ρ sm s.fp trace) :
    ExitAssertions (cells m (relocAddr ρ s.ap))
      (TraceCompleteness.traceResult m (relocAddr ρ s.ap) (trace.map (projectState ρ))) :=
  TraceCompleteness.trace_to_exitAssertions hr.canonical (start_projection hs hp.2)
    (trace_projection hr prog trace ht) (ends_projection ρ prog trace he)
    (rangecheck_projection hr hrc)

theorem trace_projection_conversionChecks {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {prog : Nat} {trace : List SegState} {s : SegState}
    (hs : trace.head? = some s) (hp : s.pc.seg = prog ∧ s.pc.off = 1274)
    (ht : SegCheckedTrace sm prog trace) (he : SegEndsAtExit prog trace)
    (hrc : SegTraceRangeChecks ρ sm s.fp trace) :
    ConversionChecks (m (relocAddr ρ s.ap + -1))
      (TraceCompleteness.traceResult m (relocAddr ρ s.ap) (trace.map (projectState ρ))) :=
  exitAssertions_to_checks (trace_projection_exitAssertions hr hs hp ht he hrc)

theorem trace_projection_rt1 {ρ : RelocTable} {sm : SegMemory} {m : Memory}
    (hr : RelocatesTo ρ sm m) {prog : Nat} {trace : List SegState} {s : SegState}
    (hs : trace.head? = some s) (hp : s.pc.seg = prog ∧ s.pc.off = 1274)
    (ht : SegCheckedTrace sm prog trace) (he : SegEndsAtExit prog trace)
    (hrc : SegTraceRangeChecks ρ sm s.fp trace) {w : Nat} (hw : w < 2 ^ 128)
    (hin : m (relocAddr ρ s.ap + -1) = rt1FieldExpr w rt1Mask) :
    TraceCompleteness.traceResult m (relocAddr ρ s.ap) (trace.map (projectState ρ)) =
      .narrow (packRotl64_1 w) :=
  rt1_exit_is_narrow hw hin (trace_projection_exitAssertions hr hs hp ht he hrc)

/-! Boundary regressions: signed offsets, typed reads, relocation and endpoints. -/
namespace Regression16d

example : addOffset ⟨2, 5⟩ (-5) = some ⟨2, 0⟩ := by decide
example : addOffset ⟨2, 4⟩ (-5) = none := by decide
example : addOffset ⟨2, 0⟩ 0 = some ⟨2, 0⟩ := by decide
example : addOffset ⟨2, 0⟩ 3 = some ⟨2, 3⟩ := by decide
example : addOffset ⟨2, 5⟩ (-5) ≠ some ⟨3, 0⟩ := by decide
example : relocAddr (fun n => (n : Int) * 100) ⟨2, 5⟩ = 205 := by decide
example : ¬ ValidValue (fun _ => -1) (.ptr ⟨0, 0⟩) := by
  unfold ValidValue relocAddr
  decide
example : ValidValue (fun _ => 0) (.ptr ⟨2, 0⟩) := by
  unfold ValidValue relocAddr
  decide
example : ¬ ValidValue (fun _ => (cairoPrime : Int)) (.ptr ⟨2, 0⟩) := by
  unfold ValidValue relocAddr
  decide
example : ¬ ValidValue (fun _ => 0) (.felt cairoPrime) := by
  unfold ValidValue
  omega
example : SegValue.felt 0 ≠ SegValue.ptr ⟨0, 0⟩ := by decide
example (p : Relocatable) (d : Int) (v : SegValue) :
    ¬ ReadAt (fun _ => none) p d v := by
  rintro ⟨q, _, h⟩
  contradiction
example : ReadAt (fun _ => some (.felt 7)) ⟨1, 5⟩ (-5) (.felt 7) :=
  ⟨⟨1, 0⟩, by decide, rfl⟩
example (p : Relocatable) (d : Int) (q : Relocatable) :
    ¬ ReadAt (fun _ => some (.felt 7)) p d (.ptr q) := by
  rintro ⟨r, _, h⟩
  have hn : SegValue.felt 7 = SegValue.ptr q := Option.some.inj h
  cases hn
example : ¬ WriteOnceExtension (fun _ => some (.felt 1))
    (fun _ => some (.felt 2)) := by
  intro h
  have hc := h ⟨0, 0⟩ (.felt 1) rfl
  contradiction
example : WriteOnceExtension (fun _ => none) (fun _ => some (.felt 2)) := by
  intro p v h
  contradiction
example : ¬ NonAliasing (fun _ => 0) (fun _ => some (.felt 1)) := by
  intro h
  have hc := h ⟨0, 0⟩ ⟨1, 0⟩ (by decide) (by decide) rfl
  have hs := congrArg Relocatable.seg hc
  contradiction
example (sm : SegMemory) (d : Decoded) : ¬ CodeRead sm 0 ⟨1, 1274⟩ d := by
  intro h
  have hs := h.segment
  contradiction
example : ¬ SegEndsAtExit 0 [] := by simp [SegEndsAtExit]
example : SegEndsAtExit 0 [⟨⟨0, 1297⟩, ⟨1, 5⟩, ⟨1, 8⟩⟩] := by
  unfold SegEndsAtExit
  decide
example : ¬ SegEndsAtExit 0 [⟨⟨1, 1297⟩, ⟨1, 5⟩, ⟨1, 8⟩⟩] := by
  unfold SegEndsAtExit
  decide
example : (projectState (fun _ => 1000) ⟨⟨0, 1274⟩, ⟨1, 5⟩, ⟨1, 8⟩⟩).pc = 1274 := rfl

/-- A concrete typed witness for the two-instruction Narrow path. -/
def narrowMemory : SegMemory := fun p =>
  if p.seg = 0 then some (.felt (blockWords[p.off - 1274]!))
  else if p.seg = 1 ∧ p.off = 95 then some (.ptr ⟨2, 0⟩)
  else if p.seg = 1 ∧ p.off = 10 then some (.felt 1)
  else some (.felt 0)

def segFrame (pc ap : Nat) : SegState := ⟨⟨0, pc⟩, ⟨1, ap⟩, ⟨1, 100⟩⟩

example : SegCheckedTrace narrowMemory 0
    [segFrame 1274 10, segFrame 1296 11, segFrame 1297 11] := by
  have h1 : SegStep narrowMemory 0 (segFrame 1274 10) (segFrame 1296 11) := by
    refine ⟨⟨0, 1, 0, -1, 1, 1, 0, 4, 2, 0, 2, 22⟩, ?_, ?_, ?_, ?_, rfl⟩
    · exact ⟨rfl, by decide, by decide, by decide,
        (Option.some.inj fetch_1274).symm, fun _ => by decide⟩
    · intro h
      contradiction
    · refine ⟨1, 22, ?_, rfl, ?_⟩
      · exact ⟨⟨1, 10⟩, by decide, by decide⟩
      · decide
    · decide
  have h2 : SegStep narrowMemory 0 (segFrame 1296 11) (segFrame 1297 11) := by
    refine ⟨⟨0, 1, -2, -5, 0, 0, 0, 0, 0, 4, 1, 0⟩, ?_, ?_, ?_, ?_, rfl⟩
    · refine ⟨rfl, by decide, by decide, by decide, (Option.some.inj fetch_1296).symm, ?_⟩
      intro h
      contradiction
    · intro _
      refine ⟨0, ⟨⟨1, 9⟩, by decide, by decide⟩, ?_⟩
      refine ⟨⟨2, 0⟩, ?_, ?_⟩
      · exact ⟨⟨1, 95⟩, by decide, by decide⟩
      · exact ⟨⟨2, 0⟩, by decide, by decide⟩
    · change addOffset ⟨0, 1296⟩ 1 = some ⟨0, 1297⟩
      decide
    · decide
  exact ⟨h1, h2, trivial⟩

example : SegRangeChecks narrowMemory ⟨1, 100⟩ 1 := by
  refine ⟨⟨2, 0⟩, ⟨⟨1, 95⟩, by decide, by decide⟩, ?_⟩
  intro i hi
  have hz : i = 0 := by omega
  subst i
  exact ⟨0, ⟨⟨2, 0⟩, by decide, by decide⟩, by decide⟩

end Regression16d

end MlDsaCasmMemoryRefinement

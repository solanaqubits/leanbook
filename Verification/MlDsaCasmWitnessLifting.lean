/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MlDsaCasmMemoryRefinement

/-! Narrow witness lifting in the abstract segmented model. The seven assignments
are finite data, not step premises. Hint cells are prepared before execution;
no actual hint algorithm, allocator or external Cairo VM is certified. -/
namespace MlDsaCasmWitnessLifting

open MlDsaRt1 MlDsaU128Conversion MlDsaProductionConversionBlock
open MlDsaCasmBlockSemantics MlDsaCasmMemoryRefinement

set_option maxRecDepth 4096

structure NarrowData where
  prog : Nat
  exec : Nat
  rcSeg : Nat
  a : Nat
  f : Nat
  rcOff : Nat
  base : RelocTable
  value : Nat

def ap0 (d : NarrowData) : Relocatable := ⟨d.exec, d.a + 1⟩
def fp0 (d : NarrowData) : Relocatable := ⟨d.exec, d.f + 5⟩
def rc0 (d : NarrowData) : Relocatable := ⟨d.rcSeg, d.rcOff⟩

/-- Three used code cells, RC pointer, input, branch hint, RC value. -/
def slotAddr (d : NarrowData) (i : Fin 7) : Relocatable :=
  match i.val with
  | 0 => ⟨d.prog, 1274⟩
  | 1 => ⟨d.prog, 1275⟩
  | 2 => ⟨d.prog, 1296⟩
  | 3 => ⟨d.exec, d.f⟩
  | 4 => ⟨d.exec, d.a⟩
  | 5 => ap0 d
  | _ => rc0 d

def slotValue (d : NarrowData) (i : Fin 7) : SegValue :=
  match i.val with
  | 0 => .felt (blockWords[0]!)
  | 1 => .felt (blockWords[1]!)
  | 2 => .felt (blockWords[22]!)
  | 3 => .ptr (rc0 d)
  | 4 => .felt d.value
  | 5 => .felt 1
  | _ => .felt d.value

/-- Pure data/range/address conditions; no execution or projection premise. -/
structure NarrowWitness extends NarrowData where
  value_lt : value < u128Bound
  prog_exec : prog ≠ exec
  prog_rc : prog ≠ rcSeg
  exec_rc : exec ≠ rcSeg
  rc_valid : ValidValue base (.ptr (rc0 toNarrowData))
  reloc_injective : Function.Injective (fun i => relocAddr base (slotAddr toNarrowData i))

theorem slotAddr_injective (w : NarrowWitness) :
    Function.Injective (slotAddr w.toNarrowData) := by
  intro i j h
  exact w.reloc_injective (congrArg (relocAddr w.base) h)

/-- Finite assignment memory; everything outside the seven slots is undefined. -/
noncomputable def narrowSegMemory (w : NarrowWitness) : SegMemory := by
  classical
  exact fun p => if h : ∃ i, slotAddr w.toNarrowData i = p then
    some (slotValue w.toNarrowData (Classical.choose h)) else none

theorem memory_slot (w : NarrowWitness) (i : Fin 7) :
    narrowSegMemory w (slotAddr w.toNarrowData i) = some (slotValue w.toNarrowData i) := by
  classical
  unfold narrowSegMemory
  rw [dif_pos ⟨i, rfl⟩]
  congr 2
  exact slotAddr_injective w (Classical.choose_spec (show ∃ j,
    slotAddr w.toNarrowData j = slotAddr w.toNarrowData i from ⟨i, rfl⟩))

theorem memory_defined_iff (w : NarrowWitness) (p : Relocatable) :
    narrowSegMemory w p ≠ none ↔ ∃ i, slotAddr w.toNarrowData i = p := by
  classical
  unfold narrowSegMemory
  split <;> simp_all

attribute [local irreducible] narrowSegMemory

/-- Initial code, RC pointer and input; both hint cells are initially absent. -/
noncomputable def initNarrowMemory (w : NarrowWitness) : SegMemory := fun p =>
  if p = slotAddr w.toNarrowData 5 ∨ p = slotAddr w.toNarrowData 6 then none
  else narrowSegMemory w p

theorem narrowSegMemory_extends_init (w : NarrowWitness) :
    WriteOnceExtension (initNarrowMemory w) (narrowSegMemory w) := by
  intro p v h
  unfold initNarrowMemory at h
  split at h
  · contradiction
  · exact h

theorem init_slot (w : NarrowWitness) (i : Fin 7) (hi : i.val < 5) :
    initNarrowMemory w (slotAddr w.toNarrowData i) = some (slotValue w.toNarrowData i) := by
  have hn5 : slotAddr w.toNarrowData i ≠ slotAddr w.toNarrowData 5 := by
    intro h
    have h' := congrArg Fin.val (slotAddr_injective w h)
    omega
  have hn6 : slotAddr w.toNarrowData i ≠ slotAddr w.toNarrowData 6 := by
    intro h
    have h' := congrArg Fin.val (slotAddr_injective w h)
    omega
  simp only [initNarrowMemory, hn5, hn6, or_self, if_false]
  exact memory_slot w i

theorem hints_initially_absent (w : NarrowWitness) :
    initNarrowMemory w (slotAddr w.toNarrowData 5) = none ∧
    initNarrowMemory w (slotAddr w.toNarrowData 6) = none := by
  simp [initNarrowMemory]

theorem write_once_consistent (w : NarrowWitness) {p : Relocatable} {v₁ v₂ : SegValue}
    (h₁ : narrowSegMemory w p = some v₁) (h₂ : narrowSegMemory w p = some v₂) :
    v₁ = v₂ := Option.some.inj (h₁.symm.trans h₂)

theorem assignment_consistent (w : NarrowWitness) {i j : Fin 7}
    (h : slotAddr w.toNarrowData i = slotAddr w.toNarrowData j) :
    slotValue w.toNarrowData i = slotValue w.toNarrowData j := by
  rw [slotAddr_injective w h]

theorem offset_to (seg a b : Nat) (d : Int) (h : (a : Int) + d = b) :
    addOffset ⟨seg, a⟩ d = some ⟨seg, b⟩ := by
  simp [addOffset, h]

/-- Ready memory contains every used operand before the first instruction. -/
theorem narrow_operands_defined (w : NarrowWitness) :
    ReadAt (narrowSegMemory w) (ap0 w.toNarrowData) 0 (.felt 1) ∧
    ReadAt (narrowSegMemory w) (ap0 w.toNarrowData) (-1) (.felt w.value) ∧
    ReadAt (narrowSegMemory w) (fp0 w.toNarrowData) (-5) (.ptr (rc0 w.toNarrowData)) ∧
    ReadAt (narrowSegMemory w) (rc0 w.toNarrowData) 0 (.felt w.value) := by
  refine ⟨⟨slotAddr w.toNarrowData 5, ?_, memory_slot w 5⟩,
    ⟨slotAddr w.toNarrowData 4, ?_, memory_slot w 4⟩,
    ⟨slotAddr w.toNarrowData 3, ?_, memory_slot w 3⟩,
    ⟨slotAddr w.toNarrowData 6, ?_, memory_slot w 6⟩⟩
  · exact offset_to w.exec (w.a + 1) (w.a + 1) 0 (by omega)
  · exact offset_to w.exec (w.a + 1) w.a (-1) (by omega)
  · exact offset_to w.exec (w.f + 5) w.f (-5) (by omega)
  · exact offset_to w.rcSeg w.rcOff w.rcOff 0 (by omega)

def segFrame (d : NarrowData) (pc delta : Nat) : SegState :=
  ⟨⟨d.prog, pc⟩, ⟨d.exec, d.a + 1 + delta⟩, fp0 d⟩

def liftNarrowTrace (w : NarrowWitness) : List SegState :=
  [segFrame w.toNarrowData 1274 0, segFrame w.toNarrowData 1296 1,
    segFrame w.toNarrowData 1297 1]

theorem narrowWitness_to_segCheckedTrace (w : NarrowWitness) :
    SegCheckedTrace (narrowSegMemory w) w.prog (liftNarrowTrace w) := by
  have ops := narrow_operands_defined w
  have h1 : SegStep (narrowSegMemory w) w.prog
      (segFrame w.toNarrowData 1274 0) (segFrame w.toNarrowData 1296 1) := by
    refine ⟨⟨0, 1, 0, -1, 1, 1, 0, 4, 2, 0, 2, 22⟩, ?_, ?_, ?_, ?_, rfl⟩
    · exact ⟨rfl, (by change 1274 ≤ 1274 ∧ 1274 - 1274 ∈ instructionOffsets; decide),
        (by
          simp only [segFrame, Nat.reduceSub]
          exact memory_slot w 0), (by simp only [segFrame, Nat.reduceSub]; decide),
        (Option.some.inj fetch_1274).symm, (by
          intro _
          simp only [segFrame, Nat.reduceSub, Nat.reduceAdd]
          exact memory_slot w 1)⟩
    · intro h
      contradiction
    · exact ⟨1, 22, ops.1, rfl, by simp [segFrame, addOffset]⟩
    · exact offset_to w.exec (w.a + 1) (w.a + 1 + 1) 1 (by omega)
  have h2 : SegStep (narrowSegMemory w) w.prog
      (segFrame w.toNarrowData 1296 1) (segFrame w.toNarrowData 1297 1) := by
    refine ⟨⟨0, 1, -2, -5, 0, 0, 0, 0, 0, 4, 1, 0⟩, ?_, ?_, ?_, ?_, rfl⟩
    · refine ⟨rfl, (by change 1274 ≤ 1296 ∧ 1296 - 1274 ∈ instructionOffsets; decide),
        (by
          simp only [segFrame, Nat.reduceSub]
          exact memory_slot w 2), (by simp only [segFrame, Nat.reduceSub]; decide),
        (Option.some.inj fetch_1296).symm, ?_⟩
      intro h
      contradiction
    · intro _
      refine ⟨w.value, ⟨slotAddr w.toNarrowData 4, ?_, memory_slot w 4⟩,
        ⟨rc0 w.toNarrowData, ops.2.2.1, ops.2.2.2⟩⟩
      exact offset_to w.exec (w.a + 1 + 1) w.a (-2) (by omega)
    · change addOffset ⟨w.prog, 1296⟩ 1 = some ⟨w.prog, 1297⟩
      simp [addOffset]
    · exact offset_to w.exec (w.a + 1 + 1) (w.a + 1 + 1) 0 (by omega)
  exact ⟨h1, h2, trivial⟩

theorem project_segFrame (w : NarrowWitness) (pc delta : Nat) :
    projectState w.base (segFrame w.toNarrowData pc delta) =
    frame (relocAddr w.base (ap0 w.toNarrowData))
      (relocAddr w.base (fp0 w.toNarrowData)) pc (delta : Int) := by
  simp [projectState, segFrame, frame, relocAddr, ap0, Int.add_assoc]

theorem project_liftNarrowTrace (w : NarrowWitness) :
    (liftNarrowTrace w).map (projectState w.base) =
    narrowTrace (relocAddr w.base (ap0 w.toNarrowData))
      (relocAddr w.base (fp0 w.toNarrowData)) := by
  simp only [liftNarrowTrace, List.map_cons, List.map_nil, project_segFrame, narrowTrace]
  rfl

theorem narrow_rangeChecks (w : NarrowWitness) :
    SegRangeChecks (narrowSegMemory w) (fp0 w.toNarrowData) 1 := by
  have ops := narrow_operands_defined w
  refine ⟨rc0 w.toNarrowData, ops.2.2.1, ?_⟩
  intro i hi
  have hz : i = 0 := by omega
  subst i
  exact ⟨w.value, ops.2.2.2, w.value_lt⟩

/-- A flat realization is constructed, not supplied as a witness premise. -/
noncomputable def narrowFlatMemory (w : NarrowWitness) : Memory := by
  classical
  exact fun addr => if h : ∃ i, relocAddr w.base (slotAddr w.toNarrowData i) = addr then
    relocVal w.base (slotValue w.toNarrowData (Classical.choose h)) else 0

theorem slot_valid (w : NarrowWitness) (i : Fin 7) :
    ValidValue w.base (slotValue w.toNarrowData i) := by
  have hv : w.value < cairoPrime := lt_trans w.value_lt (by decide)
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
  rcases hi with h | h | h | h | h | h | h <;> simp only [slotValue, h]
  · change blockWords[0]! < cairoPrime
    decide
  · change blockWords[1]! < cairoPrime
    decide
  · change blockWords[22]! < cairoPrime
    decide
  · exact w.rc_valid
  · exact hv
  · change 1 < cairoPrime
    decide
  · exact hv

theorem relocVal_lt {ρ : RelocTable} {v : SegValue} (h : ValidValue ρ v) :
    relocVal ρ v < cairoPrime := by
  cases v with
  | felt n => exact h
  | ptr p =>
    change (relocAddr ρ p).toNat < cairoPrime
    have h' := Int.toNat_of_nonneg h.1
    have hb := h.2
    omega

theorem flat_slot (w : NarrowWitness) (i : Fin 7) :
    narrowFlatMemory w (relocAddr w.base (slotAddr w.toNarrowData i)) =
      relocVal w.base (slotValue w.toNarrowData i) := by
  classical
  unfold narrowFlatMemory
  rw [dif_pos ⟨i, rfl⟩]
  have he := w.reloc_injective (Classical.choose_spec (show ∃ j,
    relocAddr w.base (slotAddr w.toNarrowData j) =
      relocAddr w.base (slotAddr w.toNarrowData i) from ⟨i, rfl⟩))
  rw [he]

theorem narrow_relocates (w : NarrowWitness) :
    RelocatesTo w.base (narrowSegMemory w) (narrowFlatMemory w) := by
  classical
  constructor
  · intro addr
    unfold narrowFlatMemory
    split
    · exact relocVal_lt (slot_valid w _)
    · decide
  · intro p v h
    have hd : narrowSegMemory w p ≠ none := by rw [h]; simp
    obtain ⟨i, rfl⟩ := (memory_defined_iff w p).mp hd
    rw [memory_slot] at h
    have hv := Option.some.inj h
    subst v
    exact ⟨slot_valid w i, flat_slot w i⟩

theorem lifted_flat_checked (w : NarrowWitness) :
    CheckedTrace (narrowFlatMemory w)
      (narrowTrace (relocAddr w.base (ap0 w.toNarrowData))
        (relocAddr w.base (fp0 w.toNarrowData))) := by
  rw [← project_liftNarrowTrace]
  exact trace_projection (narrow_relocates w) w.prog _ (narrowWitness_to_segCheckedTrace w)

namespace Regression

def sampleData (v : Nat) : NarrowData :=
  ⟨0, 1, 2, 9, 95, 0, (fun seg => (seg : Int) * 10000), v⟩

def sample (v : Nat) (hv : v < u128Bound) : NarrowWitness where
  toNarrowData := sampleData v
  value_lt := hv
  prog_exec := by change (0 : Nat) ≠ 1; decide
  prog_rc := by change (0 : Nat) ≠ 2; decide
  exec_rc := by change (1 : Nat) ≠ 2; decide
  rc_valid := by
    norm_num [ValidValue, relocAddr, rc0, sampleData, cairoPrime]
  reloc_injective := by
    change Function.Injective (fun i =>
      relocAddr (sampleData 0).base (slotAddr (sampleData 0) i))
    unfold Function.Injective
    decide

example : SegCheckedTrace (narrowSegMemory (sample 0 (by decide))) 0
    (liftNarrowTrace (sample 0 (by decide))) := narrowWitness_to_segCheckedTrace _

example : SegCheckedTrace (narrowSegMemory (sample (u128Bound - 1) (by decide))) 0
    (liftNarrowTrace (sample (u128Bound - 1) (by decide))) :=
  narrowWitness_to_segCheckedTrace _

example : (liftNarrowTrace (sample 0 (by decide))).map
    (projectState (sampleData 0).base) = narrowTrace 10010 10100 :=
  project_liftNarrowTrace _

example : (liftNarrowTrace (sample 0 (by decide))).map (fun s => s.pc.off) =
    [1274, 1296, 1297] := rfl

example : RelocatesTo (sampleData 0).base (narrowSegMemory (sample 0 (by decide)))
    (narrowFlatMemory (sample 0 (by decide))) := narrow_relocates (sample 0 (by decide))

example : SegRangeChecks (narrowSegMemory (sample 0 (by decide))) ⟨1, 100⟩ 1 :=
  narrow_rangeChecks _

example : initNarrowMemory (sample 0 (by decide)) ⟨1, 95⟩ = some (.ptr ⟨2, 0⟩) :=
  init_slot _ 3 (by decide)

example : initNarrowMemory (sample 0 (by decide)) ⟨1, 9⟩ = some (.felt 0) :=
  init_slot _ 4 (by decide)

example : initNarrowMemory (sample 0 (by decide)) ⟨1, 10⟩ = none :=
  (hints_initially_absent _).1

example : initNarrowMemory (sample 0 (by decide)) ⟨2, 0⟩ = none :=
  (hints_initially_absent _).2

example : narrowSegMemory (sample 0 (by decide)) ⟨2, 0⟩ = some (.felt 0) :=
  memory_slot _ 6

example : narrowSegMemory (sample (u128Bound - 1) (by decide)) ⟨2, 0⟩ =
    some (.felt (u128Bound - 1)) := memory_slot _ 6

example (w : NarrowWitness) : w.f ≠ w.a := by
  intro h
  have he : slotAddr w.toNarrowData 3 = slotAddr w.toNarrowData 4 := by
    change (⟨w.exec, w.f⟩ : Relocatable) = ⟨w.exec, w.a⟩
    rw [h]
  have hi := congrArg Fin.val (slotAddr_injective w he)
  contradiction

example (w : NarrowWitness) (n : Nat) :
    narrowSegMemory w (slotAddr w.toNarrowData 3) ≠ some (.felt n) := by
  rw [memory_slot]
  intro h
  have he : SegValue.ptr (rc0 w.toNarrowData) = .felt n := Option.some.inj h
  cases he

example : ¬ u128Bound < u128Bound := by omega

example : narrowSegMemory (sample 0 (by decide)) ⟨3, 0⟩ = none := by
  by_contra h
  obtain ⟨i, hi⟩ := (memory_defined_iff _ _).mp h
  have he := congrArg Relocatable.seg hi
  have hn : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
  rcases hn with hn | hn | hn | hn | hn | hn | hn <;>
    simp [slotAddr, hn, sample, sampleData, ap0, rc0] at he

end Regression


/-! Wide witnesses use the same abstract completed-memory discipline. All scalar
intermediates are constructed arithmetically before the checked trace. -/
namespace Wide

structure Data extends NarrowData where
  high : Nat
  low : Nat
  equal : Bool
  shiftedValue : Nat
  differenceValue : Nat
  adjustedValue : Nat

def shifted (d : Data) : Nat := d.shiftedValue
def difference (d : Data) : Nat := d.differenceValue
def adjusted (d : Data) : Nat := d.adjustedValue

def stackValue (d : Data) : Nat → Nat
  | 0 => d.value
  | 1 => 0
  | 2 => shifted d
  | 3 => difference d
  | 4 => adjusted d
  | 5 => d.high
  | _ => d.low

def rcValue (d : Data) : Nat → Nat
  | 0 => d.high
  | 1 => d.low
  | _ => adjusted d

/-- Code23, FP pointer1, stack7, RangeCheck3: a finite local footprint. -/
def addr (d : Data) (i : Fin 34) : Relocatable :=
  if i.val < 23 then ⟨d.prog, 1274 + i.val⟩
  else if i.val = 23 then ⟨d.exec, d.f⟩
  else if i.val < 31 then ⟨d.exec, d.a + (i.val - 24)⟩
  else ⟨d.rcSeg, d.rcOff + (i.val - 31)⟩

def val (d : Data) (i : Fin 34) : SegValue :=
  if i.val < 23 then .felt (blockWords[i.val]!)
  else if i.val = 23 then .ptr (rc0 d.toNarrowData)
  else if i.val < 31 then .felt (stackValue d (i.val - 24))
  else .felt (rcValue d (i.val - 31))

/-- Numeric and layout assumptions only; neither path nor steps are premises. -/
structure Witness extends Data where
  high_lt : high < u128Bound
  low_lt : low < u128Bound
  high_ne : high ≠ 0
  input_eq : value = (shifted toData + low) % cairoPrime
  shift_eq : shifted toData = (high * u128Bound) % cairoPrime
  diff_eq : difference toData = (high + (cairoPrime - maxHigh)) % cairoPrime
  adj_eq : adjusted toData = if equal then (low + (u128Bound - 1)) % cairoPrime
    else (high + (u128Bound - maxHigh)) % cairoPrime
  branch : if equal then high = maxHigh ∧ low = 0 else high < maxHigh
  prog_exec : prog ≠ exec
  prog_rc : prog ≠ rcSeg
  exec_rc : exec ≠ rcSeg
  rc_valid : ValidValue base (.ptr (rc0 toNarrowData))
  injective : Function.Injective (fun i => relocAddr base (addr toData i))

abbrev WideEqualWitness := {w : Witness // w.equal = true}
abbrev WideLessWitness := {w : Witness // w.equal = false}

theorem addr_injective (w : Witness) : Function.Injective (addr w.toData) := by
  intro i j h
  exact w.injective (congrArg (relocAddr w.base) h)

noncomputable def memory (w : Witness) : SegMemory := by
  classical
  exact fun p => if h : ∃ i, addr w.toData i = p then
    some (val w.toData (Classical.choose h)) else none

theorem memory_at (w : Witness) (i : Fin 34) :
    memory w (addr w.toData i) = some (val w.toData i) := by
  classical
  unfold memory
  rw [dif_pos ⟨i, rfl⟩]
  congr 2
  exact addr_injective w (Classical.choose_spec (show ∃ j,
    addr w.toData j = addr w.toData i from ⟨i, rfl⟩))

theorem memory_domain (w : Witness) (p : Relocatable) :
    memory w p ≠ none ↔ ∃ i, addr w.toData i = p := by
  classical
  unfold memory
  split <;> simp_all

attribute [local irreducible] memory

/-- Code, input and RC pointer are initial; remaining scalar cells are prepared. -/
noncomputable def initial (w : Witness) : SegMemory := by
  classical
  exact fun p => if ∃ i : Fin 34, i.val < 25 ∧ addr w.toData i = p then memory w p
    else none

theorem extends_initial (w : Witness) : WriteOnceExtension (initial w) (memory w) := by
  intro p v h
  unfold initial at h
  split at h
  · exact h
  · contradiction

theorem initial_at (w : Witness) (i : Fin 34) (hi : i.val < 25) :
    initial w (addr w.toData i) = some (val w.toData i) := by
  classical
  unfold initial
  rw [if_pos ⟨i, hi, rfl⟩]
  exact memory_at w i

theorem prepared_initially_absent (w : Witness) (i : Fin 34) (hi : 25 ≤ i.val) :
    initial w (addr w.toData i) = none := by
  classical
  unfold initial
  apply if_neg
  rintro ⟨j, hj, he⟩
  have hv := congrArg Fin.val (addr_injective w he)
  omega

theorem assignment_consistent (w : Witness) {i j : Fin 34}
    (h : addr w.toData i = addr w.toData j) : val w.toData i = val w.toData j := by
  rw [addr_injective w h]

theorem code_at (w : Witness) (k : Nat) (hk : k < 23) :
    memory w ⟨w.prog, 1274 + k⟩ = some (.felt (blockWords[k]!)) := by
  have h := memory_at w ⟨k, by omega⟩
  simpa only [addr, val, hk, if_true] using h

theorem stack_at (w : Witness) (k : Nat) (hk : k < 7) :
    memory w ⟨w.exec, w.a + k⟩ = some (.felt (stackValue w.toData k)) := by
  have h := memory_at w ⟨24 + k, by omega⟩
  have h1 : ¬24 + k < 23 := by omega
  have h2 : 24 + k ≠ 23 := by omega
  have h3 : 24 + k < 31 := by omega
  have h4 : 24 + k - 24 = k := by omega
  simpa only [addr, val, h1, h2, h3, h4, if_false, if_true] using h

theorem ptr_at (w : Witness) :
    memory w ⟨w.exec, w.f⟩ = some (.ptr (rc0 w.toNarrowData)) := memory_at w 23

theorem rc_at (w : Witness) (k : Nat) (hk : k < 3) :
    memory w ⟨w.rcSeg, w.rcOff + k⟩ = some (.felt (rcValue w.toData k)) := by
  have h := memory_at w ⟨31 + k, by omega⟩
  have h1 : ¬31 + k < 23 := by omega
  have h2 : 31 + k ≠ 23 := by omega
  have h3 : ¬31 + k < 31 := by omega
  have h4 : 31 + k - 31 = k := by omega
  simpa only [addr, val, h1, h2, h3, h4, if_false] using h

theorem stack_read (w : Witness) (delta k : Nat) (off : Int) (hk : k < 7)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + k : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (stackValue w.toData k)) :=
  ⟨⟨w.exec, w.a + k⟩, offset_to _ _ _ _ ha, stack_at w k hk⟩

theorem ptr_read (w : Witness) :
    ReadAt (memory w) (fp0 w.toNarrowData) (-5) (.ptr (rc0 w.toNarrowData)) :=
  ⟨⟨w.exec, w.f⟩, offset_to _ _ _ _ (by omega), ptr_at w⟩

theorem rc_read (w : Witness) (k : Nat) (hk : k < 3) :
    ReadAt (memory w) (rc0 w.toNarrowData) (k : Int) (.felt (rcValue w.toData k)) :=
  ⟨⟨w.rcSeg, w.rcOff + k⟩, offset_to _ _ _ _ (by omega), rc_at w k hk⟩

/-- Recover fetch information rather than re-evaluating symbolic decoded fields. -/
theorem code_read (w : Witness) (pc : Nat) (d : Decoded)
    (hf : fetch pc = some d) (hlen : pc - 1274 < 23)
    (him : d.op1Mode = 1 → pc - 1274 + 1 < 23) :
    CodeRead (memory w) w.prog ⟨w.prog, pc⟩ d := by
  unfold fetch at hf
  split at hf
  · rename_i hv
    dsimp only at hf
    split at hf
    · rename_i hs
      have hd := Option.some.inj hf
      have hp : 1274 + (pc - 1274) = pc := by omega
      refine ⟨rfl, hv, ?_, hs, hd.symm, ?_⟩
      · simpa only [hp] using code_at w (pc - 1274) hlen
      · intro hi
        have hp' : 1274 + (pc - 1274 + 1) = pc + 1 := by omega
        simpa only [hp'] using code_at w (pc - 1274 + 1) (him hi)
    · cases hf
  · cases hf

theorem difference_zero (w : Witness) (he : w.equal = true) : difference w.toData = 0 := by
  have hb := w.branch
  rw [he] at hb
  have hh : w.high = maxHigh := hb.1
  have hAP : maxHigh ≤ cairoPrime := by decide
  rw [w.diff_eq, hh, Nat.add_sub_of_le hAP, Nat.mod_self]

theorem difference_nonzero (w : Witness) (he : w.equal = false) :
    difference w.toData ≠ 0 := by
  have hb := w.branch
  rw [he] at hb
  have hh : w.high < maxHigh := hb
  have hAP : maxHigh < cairoPrime := by decide
  have hs : w.high + (cairoPrime - maxHigh) < cairoPrime := by omega
  have hp : 0 < w.high + (cairoPrime - maxHigh) := by omega
  rw [w.diff_eq, Nat.mod_eq_of_lt hs]
  omega

theorem adjusted_lt (w : Witness) : adjusted w.toData < u128Bound := by
  have hb := w.branch
  have hAU : maxHigh < u128Bound := by decide
  have hUP : u128Bound < cairoPrime := by decide
  cases he : w.equal
  · rw [he] at hb
    have hh : w.high < maxHigh := hb
    have hs : w.high + (u128Bound - maxHigh) < u128Bound := by omega
    rw [w.adj_eq, he]
    simpa only [Bool.false_eq_true, if_false, Nat.mod_eq_of_lt (lt_trans hs hUP)] using hs
  · rw [he] at hb
    have hl : w.low = 0 := hb.2
    rw [w.adj_eq, he]
    simp only [if_true, hl, Nat.zero_add]
    exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)


theorem sread0 (w : Witness) (delta : Nat) (off : Int)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + 0 : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (w.value)) := by
  simpa only [stackValue] using stack_read w delta 0 off (by decide) ha

theorem sread1 (w : Witness) (delta : Nat) (off : Int)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + 1 : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (0)) := by
  simpa only [stackValue] using stack_read w delta 1 off (by decide) ha

theorem sread2 (w : Witness) (delta : Nat) (off : Int)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + 2 : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (shifted w.toData)) := by
  simpa only [stackValue] using stack_read w delta 2 off (by decide) ha

theorem sread3 (w : Witness) (delta : Nat) (off : Int)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + 3 : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (difference w.toData)) := by
  simpa only [stackValue] using stack_read w delta 3 off (by decide) ha

theorem sread4 (w : Witness) (delta : Nat) (off : Int)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + 4 : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (adjusted w.toData)) := by
  simpa only [stackValue] using stack_read w delta 4 off (by decide) ha

theorem sread5 (w : Witness) (delta : Nat) (off : Int)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + 5 : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (w.high)) := by
  simpa only [stackValue] using stack_read w delta 5 off (by decide) ha

theorem sread6 (w : Witness) (delta : Nat) (off : Int)
    (ha : ((w.a + 1 + delta : Nat) : Int) + off = (w.a + 6 : Nat)) :
    ReadAt (memory w) ⟨w.exec, w.a + 1 + delta⟩ off (.felt (w.low)) := by
  simpa only [stackValue] using stack_read w delta 6 off (by decide) ha

theorem entry (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1274 0)
      (segFrame w.toNarrowData 1276 1) := by
  refine ⟨_, code_read w 1274 _ fetch_1274 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro h
    contradiction
  · exact ⟨0, 22, sread1 w 0 (0) (by simp), rfl, offset_to _ _ _ _ (by simp)⟩
  · exact offset_to w.exec (w.a + 1 + 0) (w.a + 1 + 1) 1 (by simp)

theorem high_read (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1276 1)
      (segFrame w.toNarrowData 1277 2) := by
  refine ⟨_, code_read w 1276 _ fetch_1276 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    exact ⟨w.high, sread5 w 1 (3) (by simp ; omega),
      ⟨rc0 w.toNarrowData, ptr_read w, rc_read w 0 (by decide)⟩⟩
  · exact offset_to w.prog 1276 1277 1 (by simp)
  · exact offset_to w.exec (w.a + 1 + 1) (w.a + 1 + 2) 1 (by simp ; omega)

theorem low_read (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1277 2)
      (segFrame w.toNarrowData 1278 3) := by
  refine ⟨_, code_read w 1277 _ fetch_1277 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    exact ⟨w.low, sread6 w 2 (3) (by simp ; omega),
      ⟨rc0 w.toNarrowData, ptr_read w, rc_read w 1 (by decide)⟩⟩
  · exact offset_to w.prog 1277 1278 1 (by simp)
  · exact offset_to w.exec (w.a + 1 + 2) (w.a + 1 + 3) 1 (by simp ; omega)

theorem shift (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1278 3)
      (segFrame w.toNarrowData 1280 4) := by
  refine ⟨_, code_read w 1278 _ fetch_1278 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    exact ⟨shifted w.toData, sread2 w 3 (-2) (by simp ; omega),
      ⟨w.high, u128Bound, sread5 w 3 (1) (by simp ; omega), rfl, w.shift_eq⟩⟩
  · exact offset_to w.prog 1278 1280 2 (by simp)
  · exact offset_to w.exec (w.a + 1 + 3) (w.a + 1 + 4) 1 (by simp ; omega)

theorem recompose (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1280 4)
      (segFrame w.toNarrowData 1281 5) := by
  refine ⟨_, code_read w 1280 _ fetch_1280 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    exact ⟨w.value, sread0 w 4 (-5) (by simp ; omega),
      ⟨shifted w.toData, w.low, sread2 w 4 (-3) (by simp ; omega),
        sread6 w 4 (1) (by simp ; omega), w.input_eq⟩⟩
  · exact offset_to w.prog 1280 1281 1 (by simp)
  · exact offset_to w.exec (w.a + 1 + 4) (w.a + 1 + 5) 1 (by simp ; omega)

theorem difference_step (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1281 5)
      (segFrame w.toNarrowData 1283 6) := by
  refine ⟨_, code_read w 1281 _ fetch_1281 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    exact ⟨difference w.toData, sread3 w 5 (-3) (by simp ; omega),
      ⟨w.high, cairoPrime - maxHigh, sread5 w 5 (-1) (by simp ; omega), rfl, w.diff_eq⟩⟩
  · exact offset_to w.prog 1281 1283 2 (by simp)
  · exact offset_to w.exec (w.a + 1 + 5) (w.a + 1 + 6) 1 (by simp ; omega)

theorem equal_branch (w : Witness) (he : w.equal = true) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1283 6)
      (segFrame w.toNarrowData 1285 6) := by
  refine ⟨_, code_read w 1283 _ fetch_1283 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro h
    contradiction
  · refine ⟨difference w.toData, 6, sread3 w 6 (-4) (by simp ; omega), rfl, ?_⟩
    rw [difference_zero w he, if_pos rfl]
    exact offset_to _ _ _ _ (by simp)
  · exact offset_to w.exec (w.a + 1 + 6) (w.a + 1 + 6) 0 (by simp)

theorem less_branch (w : Witness) (he : w.equal = false) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1283 6)
      (segFrame w.toNarrowData 1289 6) := by
  refine ⟨_, code_read w 1283 _ fetch_1283 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro h
    contradiction
  · refine ⟨difference w.toData, 6, sread3 w 6 (-4) (by simp ; omega), rfl, ?_⟩
    rw [if_neg (difference_nonzero w he)]
    exact offset_to _ _ _ _ (by simp)
  · exact offset_to w.exec (w.a + 1 + 6) (w.a + 1 + 6) 0 (by simp)

theorem equal_adjust (w : Witness) (he : w.equal = true) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1285 6)
      (segFrame w.toNarrowData 1287 6) := by
  refine ⟨_, code_read w 1285 _ fetch_1285 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    refine ⟨adjusted w.toData, sread4 w 6 (-3) (by simp ; omega),
      ⟨w.low, u128Bound - 1, sread6 w 6 (-1) (by simp ; omega), rfl, ?_⟩⟩
    simpa only [he, if_true] using w.adj_eq
  · exact offset_to w.prog 1285 1287 2 (by simp)
  · exact offset_to w.exec (w.a + 1 + 6) (w.a + 1 + 6) 0 (by simp)

theorem equal_jump (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1287 6)
      (segFrame w.toNarrowData 1291 6) := by
  refine ⟨_, code_read w 1287 _ fetch_1287 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro h
    contradiction
  · exact ⟨4, rfl, offset_to _ _ _ _ (by simp)⟩
  · exact offset_to w.exec (w.a + 1 + 6) (w.a + 1 + 6) 0 (by simp)

theorem less_adjust (w : Witness) (he : w.equal = false) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1289 6)
      (segFrame w.toNarrowData 1291 6) := by
  refine ⟨_, code_read w 1289 _ fetch_1289 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    refine ⟨adjusted w.toData, sread4 w 6 (-3) (by simp ; omega),
      ⟨w.high, u128Bound - maxHigh, sread5 w 6 (-2) (by simp ; omega), rfl, ?_⟩⟩
    simpa only [he, Bool.false_eq_true, if_false] using w.adj_eq
  · exact offset_to w.prog 1289 1291 2 (by simp)
  · exact offset_to w.exec (w.a + 1 + 6) (w.a + 1 + 6) 0 (by simp)

theorem adjust_read (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1291 6)
      (segFrame w.toNarrowData 1292 6) := by
  refine ⟨_, code_read w 1291 _ fetch_1291 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro _
    exact ⟨adjusted w.toData, sread4 w 6 (-3) (by simp ; omega),
      ⟨rc0 w.toNarrowData, ptr_read w, rc_read w 2 (by decide)⟩⟩
  · exact offset_to w.prog 1291 1292 1 (by simp)
  · exact offset_to w.exec (w.a + 1 + 6) (w.a + 1 + 6) 0 (by simp)

theorem wide_exit (w : Witness) :
    SegStep (memory w) w.prog (segFrame w.toNarrowData 1292 6)
      (segFrame w.toNarrowData 1309 6) := by
  refine ⟨_, code_read w 1292 _ fetch_1292 (by decide) (by intro _; decide),
    ?_, ?_, ?_, rfl⟩
  all_goals dsimp only [AssertionRead, ControlRead, ResultRead, Op1Read, segBase, segFrame]
  · intro h
    contradiction
  · refine ⟨w.high, 17, sread5 w 6 (-2) (by simp ; omega), rfl, ?_⟩
    rw [if_neg w.high_ne]
    exact offset_to _ _ _ _ (by simp)
  · exact offset_to w.exec (w.a + 1 + 6) (w.a + 1 + 6) 0 (by simp)

def segPrefix (w : Witness) : List SegState :=
  [segFrame w.toNarrowData 1274 0, segFrame w.toNarrowData 1276 1,
   segFrame w.toNarrowData 1277 2, segFrame w.toNarrowData 1278 3,
   segFrame w.toNarrowData 1280 4, segFrame w.toNarrowData 1281 5,
   segFrame w.toNarrowData 1283 6]

def equalTail (w : Witness) : List SegState :=
  [segFrame w.toNarrowData 1283 6, segFrame w.toNarrowData 1285 6,
   segFrame w.toNarrowData 1287 6, segFrame w.toNarrowData 1291 6,
   segFrame w.toNarrowData 1292 6, segFrame w.toNarrowData 1309 6]

def lessTail (w : Witness) : List SegState :=
  [segFrame w.toNarrowData 1283 6, segFrame w.toNarrowData 1289 6,
   segFrame w.toNarrowData 1291 6, segFrame w.toNarrowData 1292 6,
   segFrame w.toNarrowData 1309 6]

def liftWideEqualTrace (w : WideEqualWitness) : List SegState :=
  segPrefix w.val ++ (equalTail w.val).tail

def liftWideLessTrace (w : WideLessWitness) : List SegState :=
  segPrefix w.val ++ (lessTail w.val).tail

theorem equal_checked (w : WideEqualWitness) :
    SegCheckedTrace (memory w.val) w.val.prog (liftWideEqualTrace w) := by
  exact ⟨entry w.val, high_read w.val, low_read w.val, shift w.val, recompose w.val,
    difference_step w.val, equal_branch w.val w.property, equal_adjust w.val w.property,
    equal_jump w.val, adjust_read w.val, wide_exit w.val, trivial⟩

theorem less_checked (w : WideLessWitness) :
    SegCheckedTrace (memory w.val) w.val.prog (liftWideLessTrace w) := by
  exact ⟨entry w.val, high_read w.val, low_read w.val, shift w.val, recompose w.val,
    difference_step w.val, less_branch w.val w.property, less_adjust w.val w.property,
    adjust_read w.val, wide_exit w.val, trivial⟩

theorem frame_projection (w : Witness) (pc delta : Nat) :
    projectState w.base (segFrame w.toNarrowData pc delta) =
    frame (relocAddr w.base (ap0 w.toNarrowData))
      (relocAddr w.base (fp0 w.toNarrowData)) pc (delta : Int) := by
  simp [projectState, segFrame, frame, relocAddr, ap0, Int.add_assoc]

theorem equal_projection (w : WideEqualWitness) :
    (liftWideEqualTrace w).map (projectState w.val.base) =
      widePrefix (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData)) ++
      (wideEqualTail (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData))).tail := by
  simp only [liftWideEqualTrace, segPrefix, equalTail, List.tail_cons, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, frame_projection,
    widePrefix, wideEqualTail]
  rfl

theorem less_projection (w : WideLessWitness) :
    (liftWideLessTrace w).map (projectState w.val.base) =
      widePrefix (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData)) ++
      (wideLessTail (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData))).tail := by
  simp only [liftWideLessTrace, segPrefix, lessTail, List.tail_cons, List.cons_append,
    List.nil_append, List.map_cons, List.map_nil, frame_projection,
    widePrefix, wideLessTail]
  rfl

theorem rangeChecks (w : Witness) : SegRangeChecks (memory w) (fp0 w.toNarrowData) 3 := by
  refine ⟨rc0 w.toNarrowData, ptr_read w, ?_⟩
  intro i hi
  refine ⟨rcValue w.toData i, rc_read w i hi, ?_⟩
  have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl | rfl
  · exact w.high_lt
  · exact w.low_lt
  · exact adjusted_lt w



theorem stack_lt (w : Witness) (k : Nat) (hk : k < 7) :
    stackValue w.toData k < cairoPrime := by
  have hUP : u128Bound < cairoPrime := by decide
  have hP : 0 < cairoPrime := by decide
  have hn : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change w.value < cairoPrime
    rw [w.input_eq]
    exact Nat.mod_lt _ hP
  · exact hP
  · change shifted w.toData < cairoPrime
    rw [w.shift_eq]
    exact Nat.mod_lt _ hP
  · change difference w.toData < cairoPrime
    rw [w.diff_eq]
    exact Nat.mod_lt _ hP
  · exact lt_trans (adjusted_lt w) hUP
  · exact lt_trans w.high_lt hUP
  · exact lt_trans w.low_lt hUP

theorem rc_lt (w : Witness) (k : Nat) (hk : k < 3) : rcValue w.toData k < u128Bound := by
  have hn : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hn with rfl | rfl | rfl
  · exact w.high_lt
  · exact w.low_lt
  · exact adjusted_lt w

theorem code_canonical : ∀ i : Fin 23, blockWords[i.val]! < cairoPrime := by decide

theorem val_valid (w : Witness) (i : Fin 34) : ValidValue w.base (val w.toData i) := by
  unfold val
  split
  · rename_i hi
    exact code_canonical ⟨i.val, hi⟩
  · rename_i hi
    split
    · exact w.rc_valid
    · rename_i hn
      split
      · rename_i hs
        exact stack_lt w (i.val - 24) (by omega)
      · rename_i hs
        exact lt_trans (rc_lt w (i.val - 31) (by omega)) (by decide)

noncomputable def flatMemory (w : Witness) : Memory := by
  classical
  exact fun p => if h : ∃ i, relocAddr w.base (addr w.toData i) = p then
    relocVal w.base (val w.toData (Classical.choose h)) else 0

theorem flat_at (w : Witness) (i : Fin 34) :
    flatMemory w (relocAddr w.base (addr w.toData i)) = relocVal w.base (val w.toData i) := by
  classical
  unfold flatMemory
  rw [dif_pos ⟨i, rfl⟩]
  have he := w.injective (Classical.choose_spec (show ∃ j,
    relocAddr w.base (addr w.toData j) = relocAddr w.base (addr w.toData i) from ⟨i, rfl⟩))
  rw [he]

theorem relocates (w : Witness) : RelocatesTo w.base (memory w) (flatMemory w) := by
  classical
  constructor
  · intro p
    unfold flatMemory
    split
    · exact relocVal_lt (val_valid w _)
    · decide
  · intro p v h
    have hn : memory w p ≠ none := by rw [h]; simp
    obtain ⟨i, rfl⟩ := (memory_domain w p).mp hn
    rw [memory_at] at h
    have he := Option.some.inj h
    subst v
    exact ⟨val_valid w i, flat_at w i⟩

theorem equal_flat_checked (w : WideEqualWitness) :
    CheckedTrace (flatMemory w.val)
      (widePrefix (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData)) ++
      (wideEqualTail (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData))).tail) := by
  rw [← equal_projection]
  exact trace_projection (relocates w.val) w.val.prog _ (equal_checked w)

theorem less_flat_checked (w : WideLessWitness) :
    CheckedTrace (flatMemory w.val)
      (widePrefix (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData)) ++
      (wideLessTail (relocAddr w.val.base (ap0 w.val.toNarrowData))
        (relocAddr w.val.base (fp0 w.val.toNarrowData))).tail) := by
  rw [← less_projection]
  exact trace_projection (relocates w.val) w.val.prog _ (less_checked w)


theorem equal_exitAssertions (w : WideEqualWitness) :
    ExitAssertions (cells (flatMemory w.val) (relocAddr w.val.base (ap0 w.val.toNarrowData)))
      (TraceCompleteness.traceResult (flatMemory w.val)
        (relocAddr w.val.base (ap0 w.val.toNarrowData))
        ((liftWideEqualTrace w).map (projectState w.val.base))) := by
  apply trace_projection_exitAssertions (relocates w.val)
    (s := segFrame w.val.toNarrowData 1274 0) (prog := w.val.prog)
    (show (liftWideEqualTrace w).head? = some (segFrame w.val.toNarrowData 1274 0) from rfl)
    ⟨rfl, rfl⟩ (equal_checked w)
  · exact ⟨rfl, Or.inr rfl⟩
  · exact rangeChecks w.val

theorem less_exitAssertions (w : WideLessWitness) :
    ExitAssertions (cells (flatMemory w.val) (relocAddr w.val.base (ap0 w.val.toNarrowData)))
      (TraceCompleteness.traceResult (flatMemory w.val)
        (relocAddr w.val.base (ap0 w.val.toNarrowData))
        ((liftWideLessTrace w).map (projectState w.val.base))) := by
  apply trace_projection_exitAssertions (relocates w.val)
    (s := segFrame w.val.toNarrowData 1274 0) (prog := w.val.prog)
    (show (liftWideLessTrace w).head? = some (segFrame w.val.toNarrowData 1274 0) from rfl)
    ⟨rfl, rfl⟩ (less_checked w)
  · exact ⟨rfl, Or.inr rfl⟩
  · exact rangeChecks w.val

namespace Regression

def equalData : Data := {
  prog := 0, exec := 1, rcSeg := 2, a := 9, f := 95, rcOff := 0
  base := fun seg => (seg : Int) * 10000
  value := 3618502788666131213697322783095070105623107215331596699973092056135872020480,
  high := 10633823966279327296825105735305134080,
  low := 0,
  equal := true
  shiftedValue := 3618502788666131213697322783095070105623107215331596699973092056135872020480,
  differenceValue := 0,
  adjustedValue := 340282366920938463463374607431768211455 }

def equalWitness : Witness := {
  toData := equalData
  high_lt := by decide
  low_lt := by decide
  high_ne := by decide
  input_eq := by decide
  shift_eq := by decide
  diff_eq := by decide
  adj_eq := by decide
  branch := by decide
  prog_exec := by decide
  prog_rc := by decide
  exec_rc := by decide
  rc_valid := by
    norm_num [ValidValue, relocAddr, rc0, equalData, cairoPrime]
  injective := by
    unfold Function.Injective
    decide }

def lessMinData : Data := {
  prog := 0, exec := 1, rcSeg := 2, a := 9, f := 95, rcOff := 0
  base := fun seg => (seg : Int) * 10000
  value := 340282366920938463463374607431768211456, high := 1, low := 0, equal := false
  shiftedValue := 340282366920938463463374607431768211456,
  differenceValue := 3618502788666131213697322783095070105612473391365317372676266950400566886402,
  adjustedValue := 329648542954659136166549501696463077377 }

def lessMinWitness : Witness := {
  toData := lessMinData
  high_lt := by decide
  low_lt := by decide
  high_ne := by decide
  input_eq := by decide
  shift_eq := by decide
  diff_eq := by decide
  adj_eq := by decide
  branch := by decide
  prog_exec := by decide
  prog_rc := by decide
  exec_rc := by decide
  rc_valid := by
    norm_num [ValidValue, relocAddr, rc0, lessMinData, cairoPrime]
  injective := by
    unfold Function.Injective
    decide }

def lessMaxData : Data := {
  prog := 0, exec := 1, rcSeg := 2, a := 9, f := 95, rcOff := 0
  base := fun seg => (seg : Int) * 10000
  value := 3618502788666131213697322783095070105623107215331596699973092056135872020479,
  high := 10633823966279327296825105735305134079,
  low := 340282366920938463463374607431768211455,
  equal := false
  shiftedValue := 3618502788666131213697322783095070105282824848410658236509717448704103809024,
  differenceValue := 3618502788666131213697322783095070105623107215331596699973092056135872020480,
  adjustedValue := 340282366920938463463374607431768211455 }

def lessMaxWitness : Witness := {
  toData := lessMaxData
  high_lt := by decide
  low_lt := by decide
  high_ne := by decide
  input_eq := by decide
  shift_eq := by decide
  diff_eq := by decide
  adj_eq := by decide
  branch := by decide
  prog_exec := by decide
  prog_rc := by decide
  exec_rc := by decide
  rc_valid := by
    norm_num [ValidValue, relocAddr, rc0, lessMaxData, cairoPrime]
  injective := by
    unfold Function.Injective
    decide }

def equalSample : WideEqualWitness := ⟨equalWitness, rfl⟩
def lessMinSample : WideLessWitness := ⟨lessMinWitness, rfl⟩
def lessMaxSample : WideLessWitness := ⟨lessMaxWitness, rfl⟩

example : SegCheckedTrace (memory equalWitness) 0 (liftWideEqualTrace equalSample) :=
  equal_checked equalSample
example : SegCheckedTrace (memory lessMinWitness) 0 (liftWideLessTrace lessMinSample) :=
  less_checked lessMinSample
example : SegCheckedTrace (memory lessMaxWitness) 0 (liftWideLessTrace lessMaxSample) :=
  less_checked lessMaxSample
example : (liftWideEqualTrace equalSample).map (projectState equalData.base) =
    widePrefix 10010 10100 ++ (wideEqualTail 10010 10100).tail := equal_projection equalSample
example : (liftWideLessTrace lessMaxSample).map (projectState lessMaxData.base) =
    widePrefix 10010 10100 ++ (wideLessTail 10010 10100).tail := less_projection lessMaxSample
example : (liftWideEqualTrace equalSample).length = 12 := rfl
example : (liftWideLessTrace lessMinSample).length = 11 := rfl
example : (liftWideEqualTrace equalSample).getLast?.map (fun s => s.pc.off) = some 1309 := rfl
example : (liftWideLessTrace lessMinSample).getLast?.map (fun s => s.pc.off) = some 1309 := rfl
example : RelocatesTo equalData.base (memory equalWitness) (flatMemory equalWitness) :=
  relocates equalWitness
example : RelocatesTo lessMaxData.base (memory lessMaxWitness) (flatMemory lessMaxWitness) :=
  relocates lessMaxWitness
example : SegRangeChecks (memory equalWitness) ⟨1, 100⟩ 3 := rangeChecks equalWitness
example : SegRangeChecks (memory lessMinWitness) ⟨1, 100⟩ 3 := rangeChecks lessMinWitness
example : SegRangeChecks (memory lessMaxWitness) ⟨1, 100⟩ 3 := rangeChecks lessMaxWitness
example : memory equalWitness ⟨2, 1⟩ = some (.felt 0) := rc_at equalWitness 1 (by decide)
example : memory equalWitness ⟨2, 2⟩ = some (.felt (u128Bound - 1)) :=
  rc_at equalWitness 2 (by decide)
example : initial equalWitness ⟨1, 95⟩ = some (.ptr ⟨2, 0⟩) :=
  initial_at equalWitness 23 (by decide)
example : initial equalWitness ⟨1, 10⟩ = none :=
  prepared_initially_absent equalWitness 25 (by decide)
example : initial lessMinWitness ⟨2, 2⟩ = none :=
  prepared_initially_absent lessMinWitness 33 (by decide)
example (w : Witness) (n : Nat) : memory w (addr w.toData 23) ≠ some (.felt n) := by
  rw [memory_at]
  intro h
  have he := Option.some.inj h
  cases he
example (w : Witness) : w.high ≠ 0 := w.high_ne
example (w : WideEqualWitness) : w.val.low = 0 := by
  have h := w.val.branch
  rw [w.property] at h
  exact h.2
example (w : Witness) : w.f ≠ w.a := by
  intro h
  have he : addr w.toData 23 = addr w.toData 24 := by
    change (⟨w.exec, w.f⟩ : Relocatable) = ⟨w.exec, w.a⟩
    rw [h]
  have hi := addr_injective w he
  have hn := congrArg Fin.val hi
  contradiction
example : (1 : Nat) ≠ (equalData.high + (cairoPrime - maxHigh)) % cairoPrime := by decide
example : ¬ maxHigh < maxHigh := by omega

end Regression

end Wide

end MlDsaCasmWitnessLifting

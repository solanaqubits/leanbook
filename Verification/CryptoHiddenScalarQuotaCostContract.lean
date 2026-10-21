/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaStreamingContract

/-! Source-level accounting for the inclusive streaming search. The counters
belong to an instrumented semantics, not machine instructions or allocations.
All equalities hold for arbitrary rational profiles and arbitrary tolerances. -/
namespace CryptoHiddenScalarQuotaCostContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarQuotaMinimumContract

/-- An entry of the existing transition, annotated by one active update or zero
at the absorbing boundary. The arithmetic expression is unchanged. -/
def quotaCountedEntry (n : ℕ) (p : ℕ → ℚ) (old : Vector ℚ (n + 1))
    (i : Fin (n + 1)) : ℚ × ℕ :=
  if h : n ≤ i.val then (1, 0) else
    ((1 - p i.val) * old[i.val] + p i.val * old[i.val + 1]'(by omega), 1)

/-- Materialize annotated entries and sum their active-update annotations. -/
def quotaNextRowCounted (n : ℕ) (p : ℕ → ℚ) (old : Vector ℚ (n + 1)) :
    Vector ℚ (n + 1) × ℕ :=
  let entries := Vector.ofFn (quotaCountedEntry n p old)
  (entries.map Prod.fst, ∑ i : Fin (n + 1), (entries[i.val]).2)

theorem quotaNextRowCounted_value (n : ℕ) (p : ℕ → ℚ) (old : Vector ℚ (n + 1)) :
    (quotaNextRowCounted n p old).1 = quotaNextRow n p old := by
  apply Vector.ext
  intro i hi
  simp only [quotaNextRowCounted, quotaNextRow, Vector.getElem_map, Vector.getElem_ofFn]
  unfold quotaCountedEntry
  split_ifs <;> rfl

theorem quotaNextRowCounted_updates (n : ℕ) (p : ℕ → ℚ)
    (old : Vector ℚ (n + 1)) : (quotaNextRowCounted n p old).2 = n := by
  simp only [quotaNextRowCounted, Vector.getElem_ofFn]
  rw [Fin.sum_univ_castSucc]
  have hactive (i : Fin n) : (quotaCountedEntry n p old i.castSucc).2 = 1 := by
    simp [quotaCountedEntry, Nat.not_le.mpr i.isLt]
  simp only [hactive]
  simp [quotaCountedEntry]

structure SearchStats where
  checks : ℕ
  transitions : ℕ
  updates : ℕ
  deriving DecidableEq, Repr

/-- One current-row check, followed by one counted transition and the tail. -/
def SearchStats.prepend (updates : ℕ) (s : SearchStats) : SearchStats :=
  ⟨s.checks + 1, s.transitions + 1, updates + s.updates⟩

/-- The current budget is tested even at zero fuel. Only a failed check with
positive fuel constructs the next row. No counters are inferred from the result. -/
def quotaInstrumentedScan (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) :
    ℕ → ℕ → Vector ℚ (n + 1) → Option ℕ × SearchStats
  | 0, T, row =>
    (if 1 - quotaRowValue n j row ≤ ε then some T else none, ⟨1, 0, 0⟩)
  | fuel + 1, T, row =>
    if 1 - quotaRowValue n j row ≤ ε then (some T, ⟨1, 0, 0⟩)
    else
      let next := quotaNextRowCounted n p row
      let tail := quotaInstrumentedScan n p j ε fuel (T + 1) next.1
      (tail.1, SearchStats.prepend next.2 tail.2)

theorem quotaInstrumentedScan_value (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) :
    (quotaInstrumentedScan n p j ε fuel T row).1 =
      quotaStreamingScan n p j ε fuel T row := by
  induction fuel generalizing T row with
  | zero => rfl
  | succ fuel ih =>
    simp only [quotaInstrumentedScan, quotaStreamingScan]
    split_ifs <;> simp [ih, quotaNextRowCounted_value]

/-- Exact accounting at an arbitrary starting budget and arbitrary input row.
The successful budget is start + transitions; an exhausted scan uses all fuel. -/
theorem quotaInstrumentedScan_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) :
    let result := quotaInstrumentedScan n p j ε fuel T row
    result.2.checks = result.2.transitions + 1 ∧
    result.2.updates = n * result.2.transitions ∧
    result.2.transitions ≤ fuel ∧
    (match result.1 with
     | some k => k = T + result.2.transitions
     | none => result.2.transitions = fuel) := by
  induction fuel generalizing T row with
  | zero =>
    simp only [quotaInstrumentedScan]
    split_ifs <;> simp
  | succ fuel ih =>
    simp only [quotaInstrumentedScan]
    split_ifs with h
    · simp
    · have hh := ih (T + 1) (quotaNextRowCounted n p row).1
      simp only [SearchStats.prepend, quotaNextRowCounted_updates]
      dsimp only at hh
      refine ⟨by omega, ?_, by omega, ?_⟩
      · rw [hh.2.1, Nat.mul_add, Nat.mul_one, Nat.add_comm]
      · cases he : (quotaInstrumentedScan n p j ε fuel (T + 1)
          (quotaNextRowCounted n p row).1).1 <;> simp only [he] at hh ⊢ <;> omega

def chooseQuotaBudgetInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ)
    (ε : ℚ) (cap : ℕ) : Option ℕ × SearchStats :=
  quotaInstrumentedScan n p j ε cap 0 (quotaInitialRow n)

theorem chooseQuotaBudgetInstrumented_eq_streaming (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetInstrumented n p j ε cap).1 =
      chooseQuotaBudgetStreamingWithin n p j ε cap :=
  quotaInstrumentedScan_value n p j ε cap 0 (quotaInitialRow n)

theorem chooseQuotaBudgetInstrumented_eq_reference (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetInstrumented n p j ε cap).1 = chooseQuotaBudgetWithin n p j ε cap := by
  rw [chooseQuotaBudgetInstrumented_eq_streaming, chooseQuotaBudgetStreamingWithin_eq]

theorem instrumented_some_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap k : ℕ) (h : (chooseQuotaBudgetInstrumented n p j ε cap).1 = some k) :
    (chooseQuotaBudgetInstrumented n p j ε cap).2 = ⟨k + 1, k, n * k⟩ := by
  have hs := quotaInstrumentedScan_stats n p j ε cap 0 (quotaInitialRow n)
  dsimp only at hs
  rw [← chooseQuotaBudgetInstrumented] at hs
  rw [h] at hs
  have ht : (chooseQuotaBudgetInstrumented n p j ε cap).2.transitions = k := by
    simpa using hs.2.2.2.symm
  have hc : (chooseQuotaBudgetInstrumented n p j ε cap).2.checks = k + 1 := by
    rw [hs.1, ht]
  have hu : (chooseQuotaBudgetInstrumented n p j ε cap).2.updates = n * k := by
    rw [hs.2.1, ht]
  cases he : (chooseQuotaBudgetInstrumented n p j ε cap).2
  simp only [he] at hc ht hu ⊢
  simp only [hc, ht, hu]

theorem instrumented_none_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap : ℕ) (h : (chooseQuotaBudgetInstrumented n p j ε cap).1 = none) :
    (chooseQuotaBudgetInstrumented n p j ε cap).2 = ⟨cap + 1, cap, n * cap⟩ := by
  have hs := quotaInstrumentedScan_stats n p j ε cap 0 (quotaInitialRow n)
  dsimp only at hs
  rw [← chooseQuotaBudgetInstrumented] at hs
  rw [h] at hs
  have ht := hs.2.2.2
  have hc : (chooseQuotaBudgetInstrumented n p j ε cap).2.checks = cap + 1 := by
    rw [hs.1, ht]
  have hu : (chooseQuotaBudgetInstrumented n p j ε cap).2.updates = n * cap := by
    rw [hs.2.1, ht]
  cases he : (chooseQuotaBudgetInstrumented n p j ε cap).2
  simp only [he] at hc ht hu ⊢
  simp only [hc, ht, hu]

theorem instrumented_bounds (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    let s := (chooseQuotaBudgetInstrumented n p j ε cap).2
    s.checks ≤ cap + 1 ∧ s.transitions ≤ cap ∧ s.updates ≤ n * cap := by
  have hs := quotaInstrumentedScan_stats n p j ε cap 0 (quotaInitialRow n)
  dsimp only [chooseQuotaBudgetInstrumented]
  dsimp only at hs
  exact ⟨by omega, hs.2.2.1, hs.2.1 ▸ Nat.mul_le_mul_left n hs.2.2.1⟩

/-- One unit per tested budget and per materialized entry, including initial
row and absorbing entries. Profile evaluation and rational bit costs are excluded. -/
def structuralCost (n : ℕ) (s : SearchStats) : ℕ :=
  s.checks + (n + 1) * (s.transitions + 1)

/-- Explicit uniform bound, including n = 0 and cap = 0. This is a structural
unit-cost bound, not a wall-clock, allocation or bit-complexity theorem. -/
theorem structuralCost_bound (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    structuralCost n (chooseQuotaBudgetInstrumented n p j ε cap).2 ≤
      2 * (n + 1) * (cap + 1) := by
  have hs := instrumented_bounds n p j ε cap
  dsimp only at hs
  unfold structuralCost
  calc
    _ ≤ (cap + 1) + (n + 1) * (cap + 1) :=
      Nat.add_le_add hs.1 (Nat.mul_le_mul_left _ (by omega))
    _ ≤ 2 * (n + 1) * (cap + 1) := by nlinarith

structure CryptoHiddenScalarQuotaCostContractSuite : Prop where
  row_value : ∀ n p old, (quotaNextRowCounted n p old).1 = quotaNextRow n p old
  row_updates : ∀ n p old, (quotaNextRowCounted n p old).2 = n
  search : ∀ n p j ε cap, (chooseQuotaBudgetInstrumented n p j ε cap).1 =
    chooseQuotaBudgetStreamingWithin n p j ε cap
  some_stats : ∀ n p j ε cap k, (chooseQuotaBudgetInstrumented n p j ε cap).1 = some k →
    (chooseQuotaBudgetInstrumented n p j ε cap).2 = ⟨k + 1, k, n * k⟩
  none_stats : ∀ n p j ε cap, (chooseQuotaBudgetInstrumented n p j ε cap).1 = none →
    (chooseQuotaBudgetInstrumented n p j ε cap).2 = ⟨cap + 1, cap, n * cap⟩
  bound : ∀ n p j ε cap, structuralCost n (chooseQuotaBudgetInstrumented n p j ε cap).2 ≤
    2 * (n + 1) * (cap + 1)

theorem verification_suite : CryptoHiddenScalarQuotaCostContractSuite where
  row_value := quotaNextRowCounted_value
  row_updates := quotaNextRowCounted_updates
  search := chooseQuotaBudgetInstrumented_eq_streaming
  some_stats := instrumented_some_stats
  none_stats := instrumented_none_stats
  bound := structuralCost_bound
end CryptoHiddenScalarQuotaCostContract

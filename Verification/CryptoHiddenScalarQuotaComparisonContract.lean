/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaCostContract

/-! Exact source-level structural accounting for the tabular search. Absorbed
states bypass row construction. Counts exclude recursive search control, profile
evaluation, rational bit costs, compiler optimizations and instrumentation overhead. -/
namespace CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarQuotaCostContract
open CryptoHiddenScalarQuotaBudgetContract

structure TabularStats where
  checks : ℕ
  inits : ℕ
  transitions : ℕ
  updates : ℕ
  deriving DecidableEq, Repr

def TabularStats.add (a b : TabularStats) : TabularStats :=
  ⟨a.checks + b.checks, a.inits + b.inits,
    a.transitions + b.transitions, a.updates + b.updates⟩

/-- Rebuild a row, accumulating actual counted transitions from epsilon231. -/
def quotaRowInstrumented (n : ℕ) (p : ℕ → ℚ) :
    ℕ → Vector ℚ (n + 1) × TabularStats
  | 0 => (quotaInitialRow n, ⟨0, 1, 0, 0⟩)
  | T + 1 =>
    let old := quotaRowInstrumented n p T
    let next := quotaNextRowCounted n p old.1
    (next.1, ⟨0, old.2.inits, old.2.transitions + 1, old.2.updates + next.2⟩)

theorem quotaRowInstrumented_spec (n : ℕ) (p : ℕ → ℚ) (T : ℕ) :
    (quotaRowInstrumented n p T).1 = quotaRow n p T ∧
    (quotaRowInstrumented n p T).2 = ⟨0, 1, T, n * T⟩ := by
  induction T with
  | zero => exact ⟨rfl, rfl⟩
  | succ T ih =>
    simp [quotaRowInstrumented, quotaRow, quotaNextRowCounted_value,
      quotaNextRowCounted_updates, ih.1, ih.2, Nat.mul_succ]

/-- One deficit probe. The absorption guard occurs before row construction. -/
def quotaProbeInstrumented (n : ℕ) (p : ℕ → ℚ) (j T : ℕ) : ℚ × TabularStats :=
  if h : j < n then
    let row := quotaRowInstrumented n p T
    (1 - row.1[j]'(by omega), ⟨1, row.2.inits, row.2.transitions, row.2.updates⟩)
  else (0, ⟨1, 0, 0, 0⟩)

def probeCost (n j T : ℕ) : TabularStats :=
  if j < n then ⟨1, 1, T, n*T⟩ else ⟨1, 0, 0, 0⟩

theorem quotaProbeInstrumented_spec (n : ℕ) (p : ℕ → ℚ) (j T : ℕ) :
    (quotaProbeInstrumented n p j T).1 = quotaDeficitTabular n p T j ∧
    (quotaProbeInstrumented n p j T).2 = probeCost n j T := by
  simp only [quotaProbeInstrumented, quotaDeficitTabular, quotaLowerTabular, probeCost]
  split_ifs <;> simp [quotaRowInstrumented_spec]

/-- Same recursive control as searchThrough. A successful prefix suppresses
further probes; this model does not count the descent/unwinding of search control. -/
def chooseQuotaBudgetTabularInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) :
    ℕ → Option ℕ × TabularStats
  | 0 =>
    let q := quotaProbeInstrumented n p j 0
    (if q.1 ≤ ε then some 0 else none, q.2)
  | cap + 1 =>
    let prev := chooseQuotaBudgetTabularInstrumented n p j ε cap
    match prev.1 with
    | some k => (some k, prev.2)
    | none =>
      let q := quotaProbeInstrumented n p j (cap + 1)
      (if q.1 ≤ ε then some (cap + 1) else none, prev.2.add q.2)

theorem chooseQuotaBudgetTabularInstrumented_eq (n : ℕ) (p : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 =
      chooseQuotaBudgetTabularWithin n p j ε cap := by
  induction cap with
  | zero => simp [chooseQuotaBudgetTabularInstrumented, chooseQuotaBudgetTabularWithin,
      searchThrough, (quotaProbeInstrumented_spec n p j 0).1]
  | succ cap ih =>
    simp only [chooseQuotaBudgetTabularInstrumented, ih, chooseQuotaBudgetTabularWithin,
      searchThrough]
    cases hs : searchThrough (fun T => quotaDeficitTabular n p T j ≤ ε) cap <;>
      simp [(quotaProbeInstrumented_spec n p j (cap + 1)).1]

/-- Sum 0+...+t. Division is a derived presentation, not the definition. -/
def triangular : ℕ → ℕ
  | 0 => 0
  | t + 1 => triangular t + (t + 1)

theorem triangular_double (t : ℕ) : 2 * triangular t = t * (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [triangular]; nlinarith

theorem triangular_div (t : ℕ) : triangular t = t * (t + 1) / 2 := by
  rw [← triangular_double]; omega

def lastBudget (result : Option ℕ) (cap : ℕ) : ℕ := result.getD cap

def totalCost (n j t : ℕ) : TabularStats :=
  if j < n then ⟨t+1, t+1, triangular t, n * triangular t⟩ else ⟨t+1, 0, 0, 0⟩

theorem totalCost_zero (n j : ℕ) : totalCost n j 0 = probeCost n j 0 := by
  simp [totalCost, probeCost, triangular]

theorem totalCost_succ (n j t : ℕ) :
    (totalCost n j t).add (probeCost n j (t+1)) = totalCost n j (t+1) := by
  simp only [totalCost, probeCost]
  split_ifs <;> simp [TabularStats.add, triangular, Nat.mul_add]

theorem tabular_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetTabularInstrumented n p j ε cap).2 =
      totalCost n j (lastBudget (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 cap) := by
  induction cap with
  | zero =>
    simp only [chooseQuotaBudgetTabularInstrumented]
    split_ifs <;> simpa [lastBudget, totalCost_zero] using
      (quotaProbeInstrumented_spec n p j 0).2
  | succ cap ih =>
    cases he : (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 with
    | some k => simpa [chooseQuotaBudgetTabularInstrumented, he, lastBudget] using ih
    | none =>
      simp only [he, lastBudget, Option.getD_none] at ih
      simp only [chooseQuotaBudgetTabularInstrumented, he]
      split_ifs <;> simp [lastBudget, ih, (quotaProbeInstrumented_spec n p j (cap+1)).2,
        totalCost_succ]

theorem tabular_some_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap t : ℕ) (h : (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 = some t) :
    (chooseQuotaBudgetTabularInstrumented n p j ε cap).2 = totalCost n j t := by
  simpa [h, lastBudget] using tabular_stats n p j ε cap

theorem tabular_none_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap : ℕ) (h : (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 = none) :
    (chooseQuotaBudgetTabularInstrumented n p j ε cap).2 = totalCost n j cap := by
  simpa [h, lastBudget] using tabular_stats n p j ε cap

/-- In absorbed states no row is built. One probe succeeds for nonnegative
 tolerance; negative tolerance exhausts the probes, not a row recurrence. -/
theorem tabular_absorbed (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap : ℕ) (hj : n ≤ j) :
    chooseQuotaBudgetTabularInstrumented n p j ε cap =
      if 0 ≤ ε then (some 0, ⟨1, 0, 0, 0⟩) else (none, ⟨cap+1, 0, 0, 0⟩) := by
  induction cap with
  | zero => simp [chooseQuotaBudgetTabularInstrumented, quotaProbeInstrumented,
      Nat.not_lt.mpr hj]; split_ifs <;> rfl
  | succ cap ih =>
    by_cases he : 0 ≤ ε
    · simp [chooseQuotaBudgetTabularInstrumented, ih, he]
    · simp [chooseQuotaBudgetTabularInstrumented, ih, he, quotaProbeInstrumented,
        Nat.not_lt.mpr hj, TabularStats.add]

/-- Extend epsilon231's counters with the single initial row explicitly present
at the root. This wrapper preserves SearchStats and does not alter the old API. -/
def streamingStats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) : TabularStats :=
  let s := (chooseQuotaBudgetInstrumented n p j ε cap).2
  ⟨s.checks, 1, s.transitions, s.updates⟩

theorem instrumented_results_equal (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 =
      (chooseQuotaBudgetInstrumented n p j ε cap).1 := by
  rw [chooseQuotaBudgetTabularInstrumented_eq, chooseQuotaBudgetTabularWithin_eq,
    chooseQuotaBudgetInstrumented_eq_reference]

theorem streaming_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    let t := lastBudget (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 cap
    streamingStats n p j ε cap = ⟨t+1, 1, t, n*t⟩ := by
  cases he : (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 with
  | some t =>
    have hs : (chooseQuotaBudgetInstrumented n p j ε cap).1 = some t :=
      (instrumented_results_equal n p j ε cap).symm.trans he
    simp [lastBudget, streamingStats, instrumented_some_stats n p j ε cap t hs]
  | none =>
    have hs : (chooseQuotaBudgetInstrumented n p j ε cap).1 = none :=
      (instrumented_results_equal n p j ε cap).symm.trans he
    simp [lastBudget, streamingStats, instrumented_none_stats n p j ε cap hs]

theorem triangular_ge (t : ℕ) : t ≤ triangular t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [triangular]; omega

theorem triangular_strict_iff (t : ℕ) : t < triangular t ↔ 2 ≤ t := by
  have hd := triangular_double t
  constructor
  · intro h; by_contra hn
    have ht : t = 0 ∨ t = 1 := by omega
    rcases ht with rfl | rfl <;> simp [triangular] at h
  · intro h; nlinarith

theorem triangular_saving (t : ℕ) : triangular t - t = t * (t - 1) / 2 := by
  have hg := triangular_ge t
  have hd := triangular_double t
  have he : 2 * (triangular t - t) = t * (t - 1) := by
    cases t with
    | zero => rfl
    | succ t =>
      have hsub := Nat.sub_add_cancel hg
      simp only [Nat.add_sub_cancel]
      nlinarith
  rw [← he]; omega

/-- Exact active-branch formulas, including the doubled form before division. -/
theorem nonabsorbed_counts (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (hj : j < n) :
    let result := chooseQuotaBudgetTabularInstrumented n p j ε cap
    let t := lastBudget result.1 cap
    result.2.checks = t+1 ∧ result.2.inits = t+1 ∧
    2 * result.2.transitions = t*(t+1) ∧
    result.2.transitions = t*(t+1)/2 ∧ result.2.updates = n*(t*(t+1)/2) := by
  dsimp only
  rw [tabular_stats]
  simp only [totalCost, if_pos hj]
  exact ⟨trivial, trivial, triangular_double _, triangular_div _,
    congrArg (n * ·) (triangular_div _)⟩

/-- Componentwise comparison is restricted to the active branch. -/
theorem nonabsorbed_comparison (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (hj : j < n) :
    let a := (chooseQuotaBudgetTabularInstrumented n p j ε cap).2
    let b := streamingStats n p j ε cap
    a.checks = b.checks ∧ b.inits ≤ a.inits ∧
      b.transitions ≤ a.transitions ∧ b.updates ≤ a.updates := by
  dsimp only
  rw [tabular_stats, streaming_stats]
  simp only [totalCost, if_pos hj]
  exact ⟨trivial, by omega, triangular_ge _, Nat.mul_le_mul_left _ (triangular_ge _)⟩

/-- Exact savings, as natural subtraction of row-building counts. -/
theorem nonabsorbed_savings (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (hj : j < n) :
    let a := (chooseQuotaBudgetTabularInstrumented n p j ε cap).2
    let b := streamingStats n p j ε cap
    let t := lastBudget (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 cap
    a.inits - b.inits = t ∧ a.transitions - b.transitions = t*(t-1)/2 ∧
      a.updates - b.updates = n*(t*(t-1)/2) := by
  dsimp only
  rw [tabular_stats, streaming_stats]
  simp only [totalCost, if_pos hj, Nat.add_sub_cancel]
  exact ⟨trivial, triangular_saving _, by rw [← Nat.mul_sub_left_distrib, triangular_saving]⟩

/-- Initialization is strictly saved at t>=1, transitions at t>=2. Active
updates additionally need n>0; that condition already follows from j<n. -/
theorem nonabsorbed_strict (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (hj : j < n) :
    let a := (chooseQuotaBudgetTabularInstrumented n p j ε cap).2
    let b := streamingStats n p j ε cap
    let t := lastBudget (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 cap
    (b.inits < a.inits ↔ 1 ≤ t) ∧
    (b.transitions < a.transitions ↔ 2 ≤ t) ∧
    (b.updates < a.updates ↔ 2 ≤ t ∧ 0 < n) := by
  dsimp only
  rw [tabular_stats, streaming_stats]
  simp only [totalCost, if_pos hj]
  have hn : 0 < n := by omega
  exact ⟨by omega, triangular_strict_iff _, by
    rw [Nat.mul_lt_mul_left hn, triangular_strict_iff]
    simp [hn]⟩

/-- Both absorbed regimes, with the contrasting streaming row costs explicit. -/
theorem absorbed_comparison (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (hj : n ≤ j) :
    (chooseQuotaBudgetTabularInstrumented n p j ε cap).2 =
      ⟨if 0 ≤ ε then 1 else cap+1, 0, 0, 0⟩ ∧
    streamingStats n p j ε cap =
      if 0 ≤ ε then ⟨1, 1, 0, 0⟩ else ⟨cap+1, 1, cap, n*cap⟩ := by
  rw [streaming_stats, tabular_absorbed n p j ε cap hj]
  split_ifs <;> simp [lastBudget]

structure CryptoHiddenScalarQuotaComparisonContractSuite : Prop where
  rows : ∀ n p T, (quotaRowInstrumented n p T).1 = quotaRow n p T ∧
    (quotaRowInstrumented n p T).2 = ⟨0, 1, T, n*T⟩
  search : ∀ n p j ε cap, (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 =
    chooseQuotaBudgetTabularWithin n p j ε cap
  counts : ∀ n p j ε cap, (chooseQuotaBudgetTabularInstrumented n p j ε cap).2 =
    totalCost n j (lastBudget (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 cap)
  streaming : ∀ n p j ε cap,
    let t := lastBudget (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 cap
    streamingStats n p j ε cap = ⟨t+1, 1, t, n*t⟩
  triangular : ∀ t, 2 * triangular t = t*(t+1)
  comparison : ∀ n p j ε cap, j < n →
    let a := (chooseQuotaBudgetTabularInstrumented n p j ε cap).2
    let b := streamingStats n p j ε cap
    a.checks = b.checks ∧ b.inits ≤ a.inits ∧
      b.transitions ≤ a.transitions ∧ b.updates ≤ a.updates
  strict : ∀ n p j ε cap, j < n →
    let a := (chooseQuotaBudgetTabularInstrumented n p j ε cap).2
    let b := streamingStats n p j ε cap
    let t := lastBudget (chooseQuotaBudgetTabularInstrumented n p j ε cap).1 cap
    (b.inits < a.inits ↔ 1 ≤ t) ∧ (b.transitions < a.transitions ↔ 2 ≤ t) ∧
      (b.updates < a.updates ↔ 2 ≤ t ∧ 0 < n)
  absorbed : ∀ n p j ε cap, n ≤ j →
    chooseQuotaBudgetTabularInstrumented n p j ε cap =
      if 0 ≤ ε then (some 0, ⟨1, 0, 0, 0⟩) else (none, ⟨cap+1, 0, 0, 0⟩)

theorem verification_suite : CryptoHiddenScalarQuotaComparisonContractSuite where
  rows := quotaRowInstrumented_spec
  search := chooseQuotaBudgetTabularInstrumented_eq
  counts := tabular_stats
  streaming := streaming_stats
  triangular := triangular_double
  comparison := nonabsorbed_comparison
  strict := nonabsorbed_strict
  absorbed := tabular_absorbed
end CryptoHiddenScalarQuotaComparisonContract

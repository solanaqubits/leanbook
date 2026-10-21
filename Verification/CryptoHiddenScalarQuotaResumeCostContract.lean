/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaResumableContract

/-! Counted resumable search. Full retained results are preserved. Counters
exclude control guards, data packaging, stack, machine allocation and bit costs. -/
namespace CryptoHiddenScalarQuotaResumeCostContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaStreamingContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaCostContract
open CryptoHiddenScalarQuotaComparisonContract
open CryptoHiddenScalarQuotaResumableContract

/-- Count actual checks and annotated row transitions, retaining the final row. -/
def quotaResumableInstrumentedScan (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) :
    (fuel T : ℕ) → (row : Vector ℚ (n + 1)) → row = quotaRow n p T →
    (∀ t < T, ε < quotaDeficit n p t j) → QuotaSearchResult n p j ε × SearchStats
  | 0, T, row, hr, hp =>
    if h : 1 - quotaRowValue n j row ≤ ε then (.found T, ⟨1, 0, 0⟩)
    else (.exhausted (cursorOfFailure n p j ε T row hr hp h), ⟨1, 0, 0⟩)
  | fuel + 1, T, row, hr, hp =>
    if h : 1 - quotaRowValue n j row ≤ ε then (.found T, ⟨1, 0, 0⟩)
    else
      let c := cursorOfFailure n p j ε T row hr hp h
      let next := quotaNextRowCounted n p row
      let tail := quotaResumableInstrumentedScan n p j ε fuel (T + 1) next.1
        (by rw [quotaNextRowCounted_value]; exact quotaStreamingScan_row_step n p T row hr)
        (fun t ht => c.prefix_failed t (by change t ≤ T; omega))
      (tail.1, SearchStats.prepend next.2 tail.2)

/-- Equality of the entire result, including the exhausted cursor. -/
theorem scan_result (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j) :
    (quotaResumableInstrumentedScan n p j ε fuel T row hr hp).1 =
      quotaResumableScan n p j ε fuel T row hr hp := by
  induction fuel generalizing T row with
  | zero => simp only [quotaResumableInstrumentedScan, quotaResumableScan]; split_ifs <;> rfl
  | succ fuel ih =>
    simp only [quotaResumableInstrumentedScan, quotaResumableScan]
    split_ifs <;> simp [ih, quotaNextRowCounted_value]

theorem scan_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j) :
    (quotaResumableInstrumentedScan n p j ε fuel T row hr hp).2 =
      (quotaInstrumentedScan n p j ε fuel T row).2 := by
  induction fuel generalizing T row with
  | zero => simp only [quotaResumableInstrumentedScan, quotaInstrumentedScan]; split_ifs <;> rfl
  | succ fuel ih =>
    simp only [quotaResumableInstrumentedScan, quotaInstrumentedScan]
    split_ifs <;> simp [ih]

/-- Add exactly the initial row construction to epsilon231's three counters. -/
def startQuotaSearchInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    QuotaSearchResult n p j ε × TabularStats :=
  let r := quotaResumableInstrumentedScan n p j ε cap 0 (quotaInitialRow n) rfl (by omega)
  (r.1, ⟨r.2.checks, 1, r.2.transitions, r.2.updates⟩)

/-- Resume uses no row initialization. The first next-row operation precedes
all new checks, while the covered and terminal branches do neither. -/
def resumeQuotaSearchInstrumented {n : ℕ} {p : ℕ → ℚ} {j : ℕ} {ε : ℚ}
    (r : QuotaSearchResult n p j ε) (newCap : ℕ) :
    QuotaSearchResult n p j ε × TabularStats :=
  match r with
  | .found t => (.found t, ⟨0, 0, 0, 0⟩)
  | .exhausted c =>
    if h : newCap ≤ c.bound then (.exhausted c, ⟨0, 0, 0, 0⟩)
    else
      let next := quotaNextRowCounted n p c.row
      let tail := quotaResumableInstrumentedScan n p j ε (newCap - (c.bound + 1))
        (c.bound + 1) next.1
        (by rw [quotaNextRowCounted_value]
            exact quotaStreamingScan_row_step n p c.bound c.row c.row_correct)
        (fun t ht => c.prefix_failed t (by omega))
      (tail.1, ⟨tail.2.checks, 0, tail.2.transitions + 1, next.2 + tail.2.updates⟩)

theorem start_result (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (startQuotaSearchInstrumented n p j ε cap).1 = startQuotaSearch n p j ε cap :=
  scan_result n p j ε cap 0 (quotaInitialRow n) rfl (by omega)

theorem resume_result {n p j ε} (r : QuotaSearchResult n p j ε) (cap : ℕ) :
    (resumeQuotaSearchInstrumented r cap).1 = resumeQuotaSearch r cap := by
  cases r with
  | found t => rfl
  | exhausted c =>
    simp only [resumeQuotaSearchInstrumented, resumeQuotaSearch]
    split_ifs <;> simp [scan_result, quotaNextRowCounted_value]

theorem start_cold_stats (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (startQuotaSearchInstrumented n p j ε cap).2 = streamingStats n p j ε cap := by
  exact congrArg (fun s : SearchStats =>
    (⟨s.checks, 1, s.transitions, s.updates⟩ : TabularStats))
    (scan_stats n p j ε cap 0 (quotaInitialRow n) rfl (by omega))

/-- A presentation of scan counters derived from the executed scan, not used
by the executable definitions to synthesize counts from the answer. -/
theorem scan_counts (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j) :
    let r := quotaResumableInstrumentedScan n p j ε fuel T row hr hp
    let t := r.1.toOption.getD (T + fuel)
    r.2 = ⟨t - T + 1, t - T, n * (t - T)⟩ := by
  dsimp only
  rw [scan_stats, scan_result, quotaResumableScan_toOption, ← quotaInstrumentedScan_value]
  have hs := quotaInstrumentedScan_stats n p j ε fuel T row
  dsimp only at hs
  have ht : (quotaInstrumentedScan n p j ε fuel T row).2.transitions =
      (quotaInstrumentedScan n p j ε fuel T row).1.getD (T + fuel) - T := by
    cases he : (quotaInstrumentedScan n p j ε fuel T row).1 <;>
      simp only [he, Option.getD_some, Option.getD_none] at hs ⊢ <;> omega
  cases he : (quotaInstrumentedScan n p j ε fuel T row).2
  simp only [he] at hs ht ⊢
  simp only [← ht, hs.1, hs.2.1]

theorem start_counts (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    let t := (startQuotaSearchInstrumented n p j ε cap).1.toOption.getD cap
    (startQuotaSearchInstrumented n p j ε cap).2 = ⟨t + 1, 1, t, n * t⟩ := by
  have h := scan_counts n p j ε cap 0 (quotaInitialRow n) rfl (by omega)
  simpa [startQuotaSearchInstrumented] using congrArg
    (fun s : SearchStats => (⟨s.checks, 1, s.transitions, s.updates⟩ : TabularStats)) h

theorem resume_found_stats {n p j ε} (T cap : ℕ) :
    (resumeQuotaSearchInstrumented (.found T : QuotaSearchResult n p j ε) cap).2 =
      ⟨0, 0, 0, 0⟩ := rfl

theorem resume_covered {n p j ε} (c : QuotaSearchCursor n p j ε) (cap : ℕ)
    (h : cap ≤ c.bound) :
    resumeQuotaSearchInstrumented (.exhausted c) cap = (.exhausted c, ⟨0, 0, 0, 0⟩) := by
  simp [resumeQuotaSearchInstrumented, h]

theorem scan_stop_bounds (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j) :
    let t := (quotaResumableInstrumentedScan n p j ε fuel T row hr hp).1.toOption.getD (T + fuel)
    T ≤ t ∧ t ≤ T + fuel := by
  dsimp only
  rw [scan_result, quotaResumableScan_toOption]
  have hs := quotaStreamingScan_spec n p j ε fuel T row hr
  cases he : quotaStreamingScan n p j ε fuel T row <;>
    simp only [he, Option.getD_some, Option.getD_none] at hs ⊢
  · omega
  · exact ⟨hs.1, hs.2.1⟩

/-- Truncated subtraction also covers the no-work branch at a smaller cap. -/
theorem resume_exhausted_counts {n p j ε} (c : QuotaSearchCursor n p j ε) (cap : ℕ) :
    let r := resumeQuotaSearchInstrumented (.exhausted c) cap
    let d := r.1.toOption.getD cap - c.bound
    r.2 = ⟨d, 0, d, n * d⟩ := by
  by_cases h : cap ≤ c.bound
  · simp [resume_covered c cap h, QuotaSearchResult.toOption, Nat.sub_eq_zero_of_le h]
  · have hr : (quotaNextRowCounted n p c.row).1 = quotaRow n p (c.bound + 1) := by
      rw [quotaNextRowCounted_value]
      exact quotaStreamingScan_row_step n p c.bound c.row c.row_correct
    have hp : ∀ t < c.bound + 1, ε < quotaDeficit n p t j :=
      fun t ht => c.prefix_failed t (by omega)
    have hs := scan_counts n p j ε (cap - (c.bound + 1)) (c.bound + 1)
      (quotaNextRowCounted n p c.row).1 hr hp
    have hb := scan_stop_bounds n p j ε (cap - (c.bound + 1)) (c.bound + 1)
      (quotaNextRowCounted n p c.row).1 hr hp
    have hc : c.bound + 1 + (cap - (c.bound + 1)) = cap := by omega
    dsimp only at hs hb
    rw [hc] at hs hb
    simp only [resumeQuotaSearchInstrumented, dif_neg h]
    rw [hs, quotaNextRowCounted_updates]
    have hd : (quotaResumableInstrumentedScan n p j ε (cap - (c.bound + 1))
        (c.bound + 1) (quotaNextRowCounted n p c.row).1 hr hp).1.toOption.getD cap -
          (c.bound + 1) + 1 =
        (quotaResumableInstrumentedScan n p j ε (cap - (c.bound + 1))
          (c.bound + 1) (quotaNextRowCounted n p c.row).1 hr hp).1.toOption.getD cap -
            c.bound := by omega
    simp only [hd]
    congr 1
    rw [Nat.add_comm, ← Nat.mul_succ]
    exact congrArg (fun k => n * k) hd

theorem resume_success_counts {n p j ε} (c : QuotaSearchCursor n p j ε) (cap T : ℕ)
    (h : (resumeQuotaSearchInstrumented (.exhausted c) cap).1 = .found T) :
    c.bound < T ∧ T ≤ cap ∧
    (resumeQuotaSearchInstrumented (.exhausted c) cap).2 =
      ⟨T - c.bound, 0, T - c.bound, n * (T - c.bound)⟩ := by
  have hc := resume_exhausted_correct c cap
  rw [← resume_result, h] at hc
  have hb : c.bound < T := by
    by_contra hn
    exact not_lt_of_ge hc.2.1 (c.prefix_failed T (by omega))
  refine ⟨hb, hc.1, ?_⟩
  simpa [h, QuotaSearchResult.toOption] using resume_exhausted_counts c cap

theorem resume_failure_counts {n p j ε} (c c' : QuotaSearchCursor n p j ε) (cap : ℕ)
    (h : (resumeQuotaSearchInstrumented (.exhausted c) cap).1 = .exhausted c') :
    (resumeQuotaSearchInstrumented (.exhausted c) cap).2 =
      ⟨cap - c.bound, 0, cap - c.bound, n * (cap - c.bound)⟩ := by
  simpa [h, QuotaSearchResult.toOption] using resume_exhausted_counts c cap

/-- The existing epsilon231 cold counters, with the explicit single initialization. -/
theorem cold_counts (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    let t := (chooseQuotaBudgetWithin n p j ε cap).getD cap
    streamingStats n p j ε cap = ⟨t + 1, 1, t, n * t⟩ := by
  rw [← start_cold_stats]
  simpa only [start_result, startQuotaSearch_eq] using start_counts n p j ε cap

/-- Add counters from the two executed stages componentwise. -/
def twoStageQuotaSearchInstrumented (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₁ cap₂ : ℕ) : QuotaSearchResult n p j ε × TabularStats :=
  let first := startQuotaSearchInstrumented n p j ε cap₁
  let second := resumeQuotaSearchInstrumented first.1 cap₂
  (second.1, first.2.add second.2)

theorem two_stage_result (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap₁ cap₂ : ℕ) :
    (twoStageQuotaSearchInstrumented n p j ε cap₁ cap₂).1 =
      resumeQuotaSearch (startQuotaSearch n p j ε cap₁) cap₂ := by
  simp [twoStageQuotaSearchInstrumented, resume_result, start_result]

/-- All four counters agree. No probability ranges are assumed. This does not
count natural-number guards, data packaging, stack or machine operations. -/
theorem two_stage_additive (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap₁ cap₂ : ℕ)
    (hc : cap₁ ≤ cap₂) :
    (twoStageQuotaSearchInstrumented n p j ε cap₁ cap₂).2 =
      streamingStats n p j ε cap₂ := by
  change (startQuotaSearchInstrumented n p j ε cap₁).2.add
    (resumeQuotaSearchInstrumented (startQuotaSearchInstrumented n p j ε cap₁).1 cap₂).2 = _
  have hs := start_counts n p j ε cap₁
  cases he : (startQuotaSearchInstrumented n p j ε cap₁).1 with
  | found T =>
    have hm := startQuotaSearch_correct n p j ε cap₁
    rw [← start_result, he] at hm
    have hf := minimal_selected n p j ε T cap₂ hm.2 (hm.1.trans hc)
    simp only [he, QuotaSearchResult.toOption, Option.getD_some] at hs
    rw [resume_found_stats, hs, cold_counts]
    simp [hf, TabularStats.add]
  | exhausted c =>
    have hb := startQuotaSearch_bound n p j ε cap₁ c
      ((start_result n p j ε cap₁).symm.trans he)
    simp only [he, QuotaSearchResult.toOption, Option.getD_none] at hs
    have hopt : (resumeQuotaSearchInstrumented (.exhausted c) cap₂).1.toOption =
        chooseQuotaBudgetWithin n p j ε cap₂ := by
      rw [resume_result]; exact resume_exhausted_eq c cap₂
    have hlast : cap₁ ≤ (chooseQuotaBudgetWithin n p j ε cap₂).getD cap₂ := by
      rw [← hopt]
      cases hf : (resumeQuotaSearchInstrumented (.exhausted c) cap₂).1 with
      | found T =>
        have ht := (resume_success_counts c cap₂ T hf).1
        simp only [QuotaSearchResult.toOption, Option.getD_some]
        omega
      | exhausted _ => exact hc
    rw [hs, resume_exhausted_counts, hopt, hb, cold_counts]
    dsimp only [TabularStats.add]
    have ha : cap₁ + ((chooseQuotaBudgetWithin n p j ε cap₂).getD cap₂ - cap₁) =
        (chooseQuotaBudgetWithin n p j ε cap₂).getD cap₂ := by omega
    congr 1
    · omega
    · rw [← Nat.mul_add, ha]

structure CryptoHiddenScalarQuotaResumeCostContractSuite : Prop where
  start : ∀ n p j ε cap, (startQuotaSearchInstrumented n p j ε cap).1 =
    startQuotaSearch n p j ε cap
  resume : ∀ n p j ε (r : QuotaSearchResult n p j ε) cap,
    (resumeQuotaSearchInstrumented r cap).1 = resumeQuotaSearch r cap
  cold : ∀ n p j ε cap, (startQuotaSearchInstrumented n p j ε cap).2 =
    streamingStats n p j ε cap
  exhausted : ∀ n p j ε (c : QuotaSearchCursor n p j ε) cap,
    let r := resumeQuotaSearchInstrumented (.exhausted c) cap
    let d := r.1.toOption.getD cap - c.bound
    r.2 = ⟨d, 0, d, n * d⟩
  additive : ∀ n p j ε cap₁ cap₂, cap₁ ≤ cap₂ →
    (twoStageQuotaSearchInstrumented n p j ε cap₁ cap₂).2 = streamingStats n p j ε cap₂

theorem verification_suite : CryptoHiddenScalarQuotaResumeCostContractSuite where
  start := start_result
  resume := fun _ _ _ _ => resume_result
  cold := start_cold_stats
  exhausted := fun _ _ _ _ => resume_exhausted_counts
  additive := two_stage_additive
end CryptoHiddenScalarQuotaResumeCostContract

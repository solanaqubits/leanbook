/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaFastContract

/-! Resumable finite quota search. Exhausted cursors retain the actual final row
and a certificate that the entire historical prefix failed. All semantic results
hold for arbitrary rational profiles. No serialization or runtime-cost claim. -/
namespace CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaMinimumContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaStreamingContract

/-- A cursor is tied to the unchanged profile, state and tolerance. -/
structure QuotaSearchCursor (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) where
  bound : ℕ
  row : Vector ℚ (n + 1)
  row_correct : row = quotaRow n p bound
  prefix_failed : ∀ t ≤ bound, ε < quotaDeficit n p t j

/-- `found` alone is a data constructor, not a proof of minimality. -/
inductive QuotaSearchResult (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) where
  | found (budget : ℕ)
  | exhausted (cursor : QuotaSearchCursor n p j ε)

def QuotaSearchResult.toOption {n p j ε} : QuotaSearchResult n p j ε → Option ℕ
  | .found t => some t
  | .exhausted _ => none

def IsMinimalQuotaBudget (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (T : ℕ) : Prop :=
  quotaDeficit n p T j ≤ ε ∧ ∀ t < T, ε < quotaDeficit n p t j

/-- An exhausted cursor may cover more than the requested window. -/
def ResultCorrect (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    QuotaSearchResult n p j ε → Prop
  | .found t => t ≤ cap ∧ IsMinimalQuotaBudget n p j ε t
  | .exhausted c => cap ≤ c.bound

/-- Extend the known failed prefix by the actual current-row comparison. -/
def cursorOfFailure (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (T : ℕ)
    (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j)
    (hf : ¬ 1 - quotaRowValue n j row ≤ ε) : QuotaSearchCursor n p j ε where
  bound := T
  row := row
  row_correct := hr
  prefix_failed := by
    intro t ht
    by_cases he : t = T
    · subst t
      simpa [hr, quotaRowValue_correct, quotaDeficit] using lt_of_not_ge hf
    · exact hp t (by omega)

/-- Zero fuel still checks the current row. On exhaustion this returns that
same row; it does not reconstruct `quotaRow` from budget zero. Proof fields are
not executable rechecks of the prefix. -/
def quotaResumableScan (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) :
    (fuel T : ℕ) → (row : Vector ℚ (n + 1)) → row = quotaRow n p T →
    (∀ t < T, ε < quotaDeficit n p t j) → QuotaSearchResult n p j ε
  | 0, T, row, hr, hp =>
    if h : 1 - quotaRowValue n j row ≤ ε then .found T
    else .exhausted (cursorOfFailure n p j ε T row hr hp h)
  | fuel + 1, T, row, hr, hp =>
    if h : 1 - quotaRowValue n j row ≤ ε then .found T
    else
      let c := cursorOfFailure n p j ε T row hr hp h
      quotaResumableScan n p j ε fuel (T + 1) (quotaNextRow n p row)
        (quotaStreamingScan_row_step n p T row hr)
        (fun t ht => c.prefix_failed t (by change t ≤ T; omega))

theorem quotaResumableScan_toOption (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j) :
    (quotaResumableScan n p j ε fuel T row hr hp).toOption =
      quotaStreamingScan n p j ε fuel T row := by
  induction fuel generalizing T row with
  | zero => simp only [quotaResumableScan, quotaStreamingScan]; split_ifs <;> rfl
  | succ fuel ih =>
    simp only [quotaResumableScan, quotaStreamingScan]
    split_ifs
    · rfl
    · exact ih _ _ _ _

/-- The retained exhausted row is at the exact final scan budget. -/
theorem quotaResumableScan_bound (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j) :
    match quotaResumableScan n p j ε fuel T row hr hp with
    | .found _ => True
    | .exhausted c => c.bound = T + fuel := by
  induction fuel generalizing T row with
  | zero => simp only [quotaResumableScan]; split_ifs <;> simp [cursorOfFailure]
  | succ fuel ih =>
    simp only [quotaResumableScan]
    split_ifs with h
    · trivial
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (T + 1) (quotaNextRow n p row)
          (quotaStreamingScan_row_step n p T row hr)
          (fun t ht => (cursorOfFailure n p j ε T row hr hp h).prefix_failed t
            (by change t ≤ T; omega))

theorem quotaResumableScan_correct (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (fuel T : ℕ) (row : Vector ℚ (n + 1)) (hr : row = quotaRow n p T)
    (hp : ∀ t < T, ε < quotaDeficit n p t j) :
    ResultCorrect n p j ε (T + fuel) (quotaResumableScan n p j ε fuel T row hr hp) := by
  have hs := quotaStreamingScan_spec n p j ε fuel T row hr
  rw [← quotaResumableScan_toOption n p j ε fuel T row hr hp] at hs
  have hb := quotaResumableScan_bound n p j ε fuel T row hr hp
  cases he : quotaResumableScan n p j ε fuel T row hr hp with
  | found k =>
    simp only [he, QuotaSearchResult.toOption] at hs
    refine ⟨hs.2.1, hs.2.2.1, ?_⟩
    intro t ht
    by_cases h : t < T
    · exact hp t h
    · exact hs.2.2.2 t (by omega) ht
  | exhausted c =>
    simp only [he] at hb
    exact le_of_eq hb.symm

/-- Initial search through the inclusive cap, retaining its exhausted cursor. -/
def startQuotaSearch (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    QuotaSearchResult n p j ε :=
  quotaResumableScan n p j ε cap 0 (quotaInitialRow n) rfl (by omega)

/-- Initialization checks exactly budget zero. -/
def initQuotaSearch (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) :
    QuotaSearchResult n p j ε := startQuotaSearch n p j ε 0

/-- Found results are terminal. An exhausted historical horizon may exceed the
new cap; otherwise one row transition precedes scanning the new budgets only. -/
def resumeQuotaSearch {n : ℕ} {p : ℕ → ℚ} {j : ℕ} {ε : ℚ}
    (result : QuotaSearchResult n p j ε) (newCap : ℕ) : QuotaSearchResult n p j ε :=
  match result with
  | .found t => .found t
  | .exhausted c =>
    if h : newCap ≤ c.bound then .exhausted c
    else quotaResumableScan n p j ε (newCap - (c.bound + 1)) (c.bound + 1)
      (quotaNextRow n p c.row)
      (quotaStreamingScan_row_step n p c.bound c.row c.row_correct)
      (fun t ht => c.prefix_failed t (by omega))

theorem startQuotaSearch_correct (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    ResultCorrect n p j ε cap (startQuotaSearch n p j ε cap) := by
  simpa [startQuotaSearch] using
    quotaResumableScan_correct n p j ε cap 0 (quotaInitialRow n) rfl (by omega)

theorem startQuotaSearch_bound (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (c : QuotaSearchCursor n p j ε) (h : startQuotaSearch n p j ε cap = .exhausted c) :
    c.bound = cap := by
  have hb := quotaResumableScan_bound n p j ε cap 0 (quotaInitialRow n) rfl (by omega)
  change (match startQuotaSearch n p j ε cap with | .found _ => True | .exhausted c => _) at hb
  simpa [h] using hb

theorem startQuotaSearch_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ) :
    (startQuotaSearch n p j ε cap).toOption = chooseQuotaBudgetWithin n p j ε cap := by
  exact (quotaResumableScan_toOption n p j ε cap 0 (quotaInitialRow n) rfl (by omega)).trans
    (chooseQuotaBudgetStreamingWithin_eq n p j ε cap)

/-- A genuine global minimum is selected by every window containing it. -/
theorem minimal_selected (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (T cap : ℕ)
    (hm : IsMinimalQuotaBudget n p j ε T) (hc : T ≤ cap) :
    chooseQuotaBudgetWithin n p j ε cap = some T := by
  cases he : chooseQuotaBudgetWithin n p j ε cap with
  | none => exact False.elim (not_lt_of_ge hm.1
      ((chooseQuotaBudgetWithin_none_iff n p j ε cap).mp he T hc))
  | some k =>
    have hs := chooseQuotaBudgetWithin_sound n p j ε cap k he
    have hk := chooseQuotaBudgetWithin_minimal n p j ε cap k he
    have : k = T := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact not_lt_of_ge hs.2 (hm.2 k hlt)
      · exact not_lt_of_ge hm.1 (hk T hgt)
    simp [this]

theorem resultCorrect_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap : ℕ)
    (r : QuotaSearchResult n p j ε) (h : ResultCorrect n p j ε cap r) :
    r.toOption = chooseQuotaBudgetWithin n p j ε cap := by
  cases r with
  | found t => exact (minimal_selected n p j ε t cap h.2 h.1).symm
  | exhausted c =>
    apply Eq.symm
    apply (chooseQuotaBudgetWithin_none_iff n p j ε cap).mpr
    exact fun t ht => c.prefix_failed t (ht.trans h)

theorem resume_exhausted_correct {n p j ε} (c : QuotaSearchCursor n p j ε)
    (newCap : ℕ) : ResultCorrect n p j ε newCap (resumeQuotaSearch (.exhausted c) newCap) := by
  simp only [resumeQuotaSearch]
  split_ifs with h
  · exact h
  · have he : c.bound + 1 + (newCap - (c.bound + 1)) = newCap := by omega
    simpa only [he] using quotaResumableScan_correct n p j ε
      (newCap - (c.bound + 1)) (c.bound + 1) (quotaNextRow n p c.row)
      (quotaStreamingScan_row_step n p c.bound c.row c.row_correct)
      (fun t ht => c.prefix_failed t (by omega))

theorem resume_exhausted_eq {n p j ε} (c : QuotaSearchCursor n p j ε) (newCap : ℕ) :
    (resumeQuotaSearch (.exhausted c) newCap).toOption =
      chooseQuotaBudgetWithin n p j ε newCap :=
  resultCorrect_eq n p j ε newCap _ (resume_exhausted_correct c newCap)

theorem resume_exhausted_covered {n p j ε} (c : QuotaSearchCursor n p j ε)
    (newCap : ℕ) (h : newCap ≤ c.bound) :
    resumeQuotaSearch (.exhausted c) newCap = .exhausted c := by
  simp [resumeQuotaSearch, h]

/-- Every exhausted continuation retains the greatest already checked horizon. -/
theorem resume_exhausted_bound {n p j ε} (c c' : QuotaSearchCursor n p j ε)
    (newCap : ℕ) (he : resumeQuotaSearch (.exhausted c) newCap = .exhausted c') :
    c'.bound = max c.bound newCap := by
  by_cases h : newCap ≤ c.bound
  · have hc : c = c' := by simpa [resumeQuotaSearch, h] using he
    subst c'
    exact (Nat.max_eq_left h).symm
  · have hs := quotaResumableScan_bound n p j ε
      (newCap - (c.bound + 1)) (c.bound + 1) (quotaNextRow n p c.row)
      (quotaStreamingScan_row_step n p c.bound c.row c.row_correct)
      (fun t ht => c.prefix_failed t (by omega))
    have hh : quotaResumableScan n p j ε
        (newCap - (c.bound + 1)) (c.bound + 1) (quotaNextRow n p c.row)
        (quotaStreamingScan_row_step n p c.bound c.row c.row_correct)
        (fun t ht => c.prefix_failed t (by omega)) = .exhausted c' := by
      simpa [resumeQuotaSearch, h] using he
    rw [hh] at hs
    simp only at hs
    rw [Nat.max_eq_right (by omega : c.bound ≤ newCap)]
    omega

theorem resume_found_preserves {n p j ε} (T newCap : ℕ) :
    resumeQuotaSearch (.found T : QuotaSearchResult n p j ε) newCap = .found T := rfl

/-- Exact condition on the new cap when a genuine minimum is already found. -/
theorem resume_found_eq_iff {n p j ε} (T newCap : ℕ)
    (hm : IsMinimalQuotaBudget n p j ε T) :
    (resumeQuotaSearch (.found T : QuotaSearchResult n p j ε) newCap).toOption =
      chooseQuotaBudgetWithin n p j ε newCap ↔ T ≤ newCap := by
  constructor
  · intro h
    exact (chooseQuotaBudgetWithin_sound n p j ε newCap T h.symm).1
  · intro h
    exact (minimal_selected n p j ε T newCap hm h).symm

/-- Stepwise preservation for valid input results and a nonshrinking window. -/
theorem resume_correct {n p j ε} (r : QuotaSearchResult n p j ε) (cap₁ cap₂ : ℕ)
    (hr : ResultCorrect n p j ε cap₁ r) (hc : cap₁ ≤ cap₂) :
    ResultCorrect n p j ε cap₂ (resumeQuotaSearch r cap₂) := by
  cases r with
  | found t => exact ⟨hr.1.trans hc, hr.2⟩
  | exhausted c => exact resume_exhausted_correct c cap₂

theorem resume_start_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ) (cap₁ cap₂ : ℕ)
    (hc : cap₁ ≤ cap₂) :
    (resumeQuotaSearch (startQuotaSearch n p j ε cap₁) cap₂).toOption =
      chooseQuotaBudgetWithin n p j ε cap₂ :=
  resultCorrect_eq n p j ε cap₂ _
    (resume_correct _ cap₁ cap₂ (startQuotaSearch_correct n p j ε cap₁) hc)

theorem resume_twice_eq (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (cap₁ cap₂ cap₃ : ℕ) (h₁₂ : cap₁ ≤ cap₂) (h₂₃ : cap₂ ≤ cap₃) :
    (resumeQuotaSearch (resumeQuotaSearch (startQuotaSearch n p j ε cap₁) cap₂) cap₃).toOption =
      chooseQuotaBudgetWithin n p j ε cap₃ :=
  resultCorrect_eq n p j ε cap₃ _
    (resume_correct _ cap₂ cap₃
      (resume_correct _ cap₁ cap₂ (startQuotaSearch_correct n p j ε cap₁) h₁₂) h₂₃)

structure CryptoHiddenScalarQuotaResumableContractSuite : Prop where
  start : ∀ n p j ε cap, (startQuotaSearch n p j ε cap).toOption =
    chooseQuotaBudgetWithin n p j ε cap
  exhausted : ∀ n p j ε (c : QuotaSearchCursor n p j ε) cap,
    (resumeQuotaSearch (.exhausted c) cap).toOption = chooseQuotaBudgetWithin n p j ε cap
  found : ∀ n p j ε t cap, IsMinimalQuotaBudget n p j ε t →
    ((resumeQuotaSearch (.found t : QuotaSearchResult n p j ε) cap).toOption =
      chooseQuotaBudgetWithin n p j ε cap ↔ t ≤ cap)
  retained_bound : ∀ n p j ε (c c' : QuotaSearchCursor n p j ε) cap,
    resumeQuotaSearch (.exhausted c) cap = .exhausted c' → c'.bound = max c.bound cap
  continuation : ∀ n p j ε cap₁ cap₂, cap₁ ≤ cap₂ →
    (resumeQuotaSearch (startQuotaSearch n p j ε cap₁) cap₂).toOption =
      chooseQuotaBudgetWithin n p j ε cap₂

theorem verification_suite : CryptoHiddenScalarQuotaResumableContractSuite where
  start := startQuotaSearch_eq
  exhausted := fun _ _ _ _ => resume_exhausted_eq
  found := fun _ _ _ _ => resume_found_eq_iff
  retained_bound := fun _ _ _ _ => resume_exhausted_bound
  continuation := resume_start_eq
end CryptoHiddenScalarQuotaResumableContract

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaChainContract

/-! Typed, untrusted cursor data. Restoration reruns the entire inclusive prefix
and compares the saved row exactly. No byte codec, provenance, profile transfer,
resource bound or authorization follows from these mathematical invariants. -/
namespace CryptoHiddenScalarQuotaSnapshotContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaChainContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaMinimumContract

structure QuotaCursorSnapshot where
  bound : ℕ
  row : List ℚ
  deriving DecidableEq, Repr

def snapshotCursor {n p j ε} (c : QuotaSearchCursor n p j ε) : QuotaCursorSnapshot :=
  ⟨c.bound, c.row.toList⟩

/-- Semantic validity relative to the externally supplied parameters. -/
def ValidSnapshot (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (s : QuotaCursorSnapshot) : Prop :=
  s.row.length = n + 1 ∧ s.row = (quotaRow n p s.bound).toList ∧
    ∀ t ≤ s.bound, ε < quotaDeficit n p t j

/-- Decidable rational equality; the reconstructed cursor supplies both proofs.
The inexpensive length guard precedes the cold search. -/
def restoreCursor? (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (s : QuotaCursorSnapshot) : Option (QuotaSearchCursor n p j ε) :=
  if s.row.length = n + 1 then
    match startQuotaSearch n p j ε s.bound with
    | .found _ => none
    | .exhausted c => if s.row = c.row.toList then some c else none
  else none

theorem snapshot_valid {n p j ε} (c : QuotaSearchCursor n p j ε) :
    ValidSnapshot n p j ε (snapshotCursor c) := by
  refine ⟨by simp [snapshotCursor], ?_, c.prefix_failed⟩
  change c.row.toList = (quotaRow n p c.bound).toList
  rw [c.row_correct]

/-- Successful restoration fixes the exact bound and row, not only a projection. -/
theorem restore_sound {n p j ε} (s : QuotaCursorSnapshot)
    (c : QuotaSearchCursor n p j ε) (h : restoreCursor? n p j ε s = some c) :
    ValidSnapshot n p j ε s ∧ snapshotCursor c = s := by
  unfold restoreCursor? at h
  split at h
  next hlen =>
    cases hs : startQuotaSearch n p j ε s.bound with
    | found t => simp [hs] at h
    | exhausted d =>
      simp only [hs] at h
      split at h
      next hrow =>
        have hdc : d = c := Option.some.inj h
        subst d
        have hb := startQuotaSearch_bound n p j ε s.bound c hs
        have hr : s.row = (quotaRow n p s.bound).toList := by
          rw [hrow, c.row_correct, hb]
        refine ⟨⟨hlen, hr, ?_⟩, ?_⟩
        · simpa only [hb] using c.prefix_failed
        · cases s
          simp_all [snapshotCursor]
      next hrow => simp at h
  next hlen => simp at h

theorem restore_complete {n p j ε} (s : QuotaCursorSnapshot)
    (hv : ValidSnapshot n p j ε s) :
    ∃ c, restoreCursor? n p j ε s = some c := by
  cases hs : startQuotaSearch n p j ε s.bound with
  | found t =>
    have hc := startQuotaSearch_correct n p j ε s.bound
    rw [hs] at hc
    exact False.elim (not_lt_of_ge hc.2.1 (hv.2.2 t hc.1))
  | exhausted c =>
    have hb := startQuotaSearch_bound n p j ε s.bound c hs
    have hr : s.row = c.row.toList := by rw [c.row_correct, hb]; exact hv.2.1
    exact ⟨c, by simp [restoreCursor?, hs, hr]⟩

theorem restore_isSome_iff {n p j ε} (s : QuotaCursorSnapshot) :
    (restoreCursor? n p j ε s).isSome = true ↔ ValidSnapshot n p j ε s := by
  constructor
  · intro h
    cases he : restoreCursor? n p j ε s with
    | none => simp [he] at h
    | some c => exact (restore_sound s c he).1
  · intro hv
    obtain ⟨c, hc⟩ := restore_complete s hv
    simp [hc]

/-- Equality of certified cursors uses their bound and proof irrelevance. -/
theorem restore_snapshot {n p j ε} (c : QuotaSearchCursor n p j ε) :
    restoreCursor? n p j ε (snapshotCursor c) = some c := by
  obtain ⟨d, hd⟩ := restore_complete (snapshotCursor c) (snapshot_valid c)
  have hb := congrArg QuotaCursorSnapshot.bound (restore_sound _ d hd).2
  have he : d = c := cursor_ext d c hb
  simpa only [he] using hd

/-- A particular successful output also requires matching that cursor's snapshot. -/
theorem restore_eq_some_iff {n p j ε} (s : QuotaCursorSnapshot)
    (c : QuotaSearchCursor n p j ε) :
    restoreCursor? n p j ε s = some c ↔
      ValidSnapshot n p j ε s ∧ snapshotCursor c = s := by
  constructor
  · exact restore_sound s c
  · rintro ⟨_, hs⟩
    rw [← hs]
    exact restore_snapshot c

theorem restore_none_iff {n p j ε} (s : QuotaCursorSnapshot) :
    restoreCursor? n p j ε s = none ↔ ¬ ValidSnapshot n p j ε s := by
  constructor
  · intro he hv
    obtain ⟨c, hc⟩ := restore_complete s hv
    simp [he] at hc
  · intro hv
    cases he : restoreCursor? n p j ε s with
    | none => rfl
    | some c => exact False.elim (hv (restore_sound s c he).1)

/-- A genuine cursor equals a cold exhausted result at its historical horizon. -/
theorem start_at_cursor {n p j ε} (c : QuotaSearchCursor n p j ε) :
    startQuotaSearch n p j ε c.bound = .exhausted c := by
  cases hs : startQuotaSearch n p j ε c.bound with
  | found t =>
    have hc := startQuotaSearch_correct n p j ε c.bound
    rw [hs] at hc
    exact False.elim (not_lt_of_ge hc.2.1 (c.prefix_failed t hc.1))
  | exhausted d =>
    have hb := startQuotaSearch_bound n p j ε c.bound d hs
    exact congrArg QuotaSearchResult.exhausted (cursor_ext d c hb)

/-- Full equality with cold search for nonshrinking bounds, including retained row. -/
theorem restore_resume_eq {n p j ε} (s : QuotaCursorSnapshot)
    (c : QuotaSearchCursor n p j ε) (h : restoreCursor? n p j ε s = some c)
    (newBound : ℕ) (hb : s.bound ≤ newBound) :
    resumeQuotaSearch (.exhausted c) newBound = startQuotaSearch n p j ε newBound := by
  have hc : c.bound = s.bound := congrArg QuotaCursorSnapshot.bound (restore_sound s c h).2
  rw [← start_at_cursor c]
  exact resumeQuotaSearch_startQuotaSearch n p j ε c.bound newBound (by omega)

/-- Any restored cursor can resume even to a smaller cap; the historical horizon
may then remain larger. This theorem concerns correctness, not full cold equality. -/
theorem restored_resume_correct {n p j ε} (s : QuotaCursorSnapshot)
    (c : QuotaSearchCursor n p j ε) (_h : restoreCursor? n p j ε s = some c)
    (newBound : ℕ) :
    ResultCorrect n p j ε newBound (resumeQuotaSearch (.exhausted c) newBound) :=
  resume_exhausted_correct c newBound

structure CryptoHiddenScalarQuotaSnapshotContractSuite : Prop where
  validity : ∀ n p j ε s, (restoreCursor? n p j ε s).isSome = true ↔ ValidSnapshot n p j ε s
  output : ∀ n p j ε s (c : QuotaSearchCursor n p j ε),
    restoreCursor? n p j ε s = some c ↔ ValidSnapshot n p j ε s ∧ snapshotCursor c = s
  round_trip : ∀ n p j ε (c : QuotaSearchCursor n p j ε),
    restoreCursor? n p j ε (snapshotCursor c) = some c
  resume : ∀ n p j ε s (c : QuotaSearchCursor n p j ε),
    restoreCursor? n p j ε s = some c → ∀ b, s.bound ≤ b →
      resumeQuotaSearch (.exhausted c) b = startQuotaSearch n p j ε b

theorem verification_suite : CryptoHiddenScalarQuotaSnapshotContractSuite where
  validity := fun _ _ _ _ => restore_isSome_iff
  output := fun _ _ _ _ => restore_eq_some_iff
  round_trip := fun _ _ _ _ => restore_snapshot
  resume := fun _ _ _ _ => restore_resume_eq
end CryptoHiddenScalarQuotaSnapshotContract

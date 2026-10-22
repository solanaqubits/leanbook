/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaSnapshotContract

/-! Finite profile transfer. Only states i<n affect quota evolution. The total
zero extension is an implementation choice, not recovery of an arbitrary function.
Independent expected parameters remain external; no provenance or resource claim. -/
namespace CryptoHiddenScalarQuotaProfileContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaTabularContract
open CryptoHiddenScalarQuotaResumableContract
open CryptoHiddenScalarQuotaSnapshotContract

/-- Materialize exactly the relevant state indices, not a time-indexed profile. -/
def exportProfile (n : ℕ) (p : ℕ → ℚ) : List ℚ :=
  List.ofFn (fun i : Fin n => p i)

/-- Total extension; values beyond the finite list are deliberately zero. -/
def profileFunction (xs : List ℚ) (i : ℕ) : ℚ := xs[i]?.getD 0

/-- Extensional agreement on the complete relevant state domain. -/
def Agrees (n : ℕ) (p q : ℕ → ℚ) : Prop := ∀ i < n, p i = q i

/-- An unchecked list must match independent n and expected coefficients exactly. -/
def Matches (n : ℕ) (expected : ℕ → ℚ) (xs : List ℚ) : Prop :=
  xs.length = n ∧ ∀ i : Fin n, profileFunction xs i = expected i

instance (n expected xs) : Decidable (Matches n expected xs) :=
  inferInstanceAs (Decidable (xs.length = n ∧ ∀ i : Fin n, profileFunction xs i = expected i))

theorem export_length (n p) : (exportProfile n p).length = n := by
  simp [exportProfile]

theorem export_agrees (n p) : Agrees n (profileFunction (exportProfile n p)) p := by
  intro i hi
  simp [profileFunction, exportProfile, hi]

theorem export_matches (n p) : Matches n p (exportProfile n p) := by
  exact ⟨export_length n p, fun i => export_agrees n p i i.isLt⟩

theorem matches_agrees {n p xs} (h : Matches n p xs) :
    Agrees n (profileFunction xs) p := by
  intro i hi
  exact h.2 ⟨i, hi⟩

/-- Every accepted finite representation is the exact materialized list. -/
theorem matches_iff (n p xs) : Matches n p xs ↔ xs = exportProfile n p := by
  constructor
  · rintro ⟨hlen, h⟩
    apply List.ext_getElem
    · simpa [exportProfile] using hlen
    · intro i hi hj
      have he := h ⟨i, by omega⟩
      simpa [profileFunction, exportProfile, List.getElem?_eq_getElem hi] using he
  · intro h
    subst xs
    exact export_matches n p

theorem quotaLower_agrees {n p q} (h : Agrees n p q) (t j : ℕ) :
    quotaLower n p t j = quotaLower n q t j := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    by_cases hj : n ≤ j
    · simp [quotaLower, hj]
    · simp only [quotaLower, if_neg hj, h j (by omega), ih]

theorem quotaDeficit_agrees {n p q} (h : Agrees n p q) (t j : ℕ) :
    quotaDeficit n p t j = quotaDeficit n q t j := by
  simp only [quotaDeficit, quotaLower_agrees h]

theorem quotaRow_agrees {n p q} (h : Agrees n p q) (t : ℕ) :
    quotaRow n p t = quotaRow n q t := by
  apply Vector.ext
  intro i hi
  simp only [quotaRow_correct, quotaLower_agrees h]

theorem validSnapshot_agrees {n p q} (h : Agrees n p q) (j ε s) :
    ValidSnapshot n p j ε s ↔ ValidSnapshot n q j ε s := by
  simp only [ValidSnapshot, quotaRow_agrees h, quotaDeficit_agrees h]

/-- Compare observable snapshots rather than equating differently indexed cursors. -/
theorem restore_projection {n p j ε} (s : QuotaCursorSnapshot) :
    (restoreCursor? n p j ε s).map snapshotCursor =
      @ite (Option QuotaCursorSnapshot) (ValidSnapshot n p j ε s)
        (Classical.propDecidable _) (some s) none := by
  classical
  cases he : restoreCursor? n p j ε s with
  | none => simp [(restore_none_iff s).mp he]
  | some c => simp [(restore_sound s c he).1, (restore_sound s c he).2]

theorem restore_agrees {n p q} (h : Agrees n p q) (j ε s) :
    (restoreCursor? n p j ε s).map snapshotCursor =
      (restoreCursor? n q j ε s).map snapshotCursor := by
  classical
  rw [restore_projection, restore_projection, validSnapshot_agrees h]

/-- Expected n/p/j/epsilon are supplied by the caller, never inferred from xs.
No search is started when the finite profile does not match expected context. -/
def restoreTransferred? (n : ℕ) (expected : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (xs : List ℚ) (s : QuotaCursorSnapshot) :
    Option (QuotaSearchCursor n (profileFunction xs) j ε) :=
  if Matches n expected xs then restoreCursor? n (profileFunction xs) j ε s else none

theorem transferred_isSome_iff (n expected j ε xs s) :
    (restoreTransferred? n expected j ε xs s).isSome = true ↔
      Matches n expected xs ∧ ValidSnapshot n expected j ε s := by
  unfold restoreTransferred?
  split
  next hm =>
    simp only [restore_isSome_iff, validSnapshot_agrees (matches_agrees hm), hm, true_and]
  next hm => simp [hm]

theorem transferred_output {n expected j ε xs s}
    (c : QuotaSearchCursor n (profileFunction xs) j ε)
    (h : restoreTransferred? n expected j ε xs s = some c) :
    Matches n expected xs ∧ ValidSnapshot n expected j ε s ∧ snapshotCursor c = s := by
  unfold restoreTransferred? at h
  split at h
  next hm =>
    have hs := restore_sound s c h
    exact ⟨hm, (validSnapshot_agrees (matches_agrees hm) j ε s).mp hs.1, hs.2⟩
  next => simp at h

theorem transferred_export (n p j ε s) :
    (restoreTransferred? n p j ε (exportProfile n p) s).map snapshotCursor =
      (restoreCursor? n p j ε s).map snapshotCursor := by
  simp only [restoreTransferred?, export_matches]
  exact restore_agrees (export_agrees n p) j ε s

structure CryptoHiddenScalarQuotaProfileContractSuite : Prop where
  canonical : ∀ n p xs, Matches n p xs ↔ xs = exportProfile n p
  row : ∀ n p t, quotaRow n (profileFunction (exportProfile n p)) t = quotaRow n p t
  acceptance : ∀ n p j ε xs s, (restoreTransferred? n p j ε xs s).isSome = true ↔
    Matches n p xs ∧ ValidSnapshot n p j ε s
  preservation : ∀ n p j ε s,
    (restoreTransferred? n p j ε (exportProfile n p) s).map snapshotCursor =
      (restoreCursor? n p j ε s).map snapshotCursor

theorem verification_suite : CryptoHiddenScalarQuotaProfileContractSuite where
  canonical := matches_iff
  row := fun n p => quotaRow_agrees (export_agrees n p)
  acceptance := transferred_isSome_iff
  preservation := transferred_export
end CryptoHiddenScalarQuotaProfileContract

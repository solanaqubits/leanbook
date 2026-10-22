/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaSnapshotContract

/-! Strict structured rational data. This API neither parses bytes nor certifies
snapshot semantics until the separate restoration step is invoked. -/
namespace CryptoHiddenScalarQuotaCanonicalWireContract
open CryptoHiddenScalarQuotaSnapshotContract
open CryptoHiddenScalarQuotaResumableContract

structure RatWire where
  num : ℤ
  den : ℕ
  deriving DecidableEq, Repr

structure QuotaSnapshotWire where
  bound : ℕ
  row : List RatWire
  deriving DecidableEq, Repr

def CanonicalRatWire (w : RatWire) : Prop :=
  0 < w.den ∧ w.num.natAbs.Coprime w.den

instance (w : RatWire) : Decidable (CanonicalRatWire w) :=
  inferInstanceAs (Decidable (0 < w.den ∧ w.num.natAbs.Coprime w.den))

def CanonicalSnapshotWire (w : QuotaSnapshotWire) : Prop :=
  ∀ q ∈ w.row, CanonicalRatWire q

def encodeRatCanonical (q : ℚ) : RatWire := ⟨q.num, q.den⟩

def decodeRatCanonical? (w : RatWire) : Option ℚ :=
  if h_pos : 0 < w.den then
    if h_coprime : w.num.natAbs.Coprime w.den then
      some (Rat.mk' w.num w.den (Nat.ne_of_gt h_pos) h_coprime)
    else none
  else none

def encodeSnapshotCanonical (s : QuotaCursorSnapshot) : QuotaSnapshotWire :=
  ⟨s.bound, s.row.map encodeRatCanonical⟩

def decodeSnapshotCanonical? (w : QuotaSnapshotWire) : Option QuotaCursorSnapshot := do
  let row ← w.row.mapM decodeRatCanonical?
  pure ⟨w.bound, row⟩

def restoreFromExternal? (n : ℕ) (p : ℕ → ℚ) (j : ℕ) (ε : ℚ)
    (w : QuotaSnapshotWire) : Option (QuotaSearchCursor n p j ε) :=
  (decodeSnapshotCanonical? w).bind (restoreCursor? n p j ε)

@[simp] theorem decode_encode_rat (q : ℚ) :
    decodeRatCanonical? (encodeRatCanonical q) = some q := by
  unfold decodeRatCanonical? encodeRatCanonical
  dsimp only
  rw [dif_pos q.den_pos, dif_pos q.reduced]

theorem encode_of_decode_rat {w : RatWire} {q : ℚ}
    (h : decodeRatCanonical? w = some q) : encodeRatCanonical q = w := by
  unfold decodeRatCanonical? at h
  split at h
  next hp =>
    split at h
    next hc =>
      have he := Option.some.inj h
      rw [← he]
      rfl
    next hc => simp at h
  next hp => simp at h

/-- No separate canonicality hypothesis: either side entails it. -/
theorem decode_rat_iff (w : RatWire) (q : ℚ) :
    decodeRatCanonical? w = some q ↔ encodeRatCanonical q = w := by
  constructor
  · exact encode_of_decode_rat
  · intro h; rw [← h]; exact decode_encode_rat q

theorem decode_rat_isSome_iff (w : RatWire) :
    (decodeRatCanonical? w).isSome = true ↔ CanonicalRatWire w := by
  by_cases hp : 0 < w.den <;> by_cases hc : w.num.natAbs.Coprime w.den <;>
    simp [decodeRatCanonical?, CanonicalRatWire, hp, hc]

theorem canonical_zero_iff (d : ℕ) : CanonicalRatWire ⟨0, d⟩ ↔ d = 1 := by
  simp only [CanonicalRatWire, Int.natAbs_zero, Nat.coprime_zero_left]
  constructor
  · exact And.right
  · intro h; subst d; exact ⟨by decide, rfl⟩

theorem encode_rat_injective : Function.Injective encodeRatCanonical := by
  intro q r h
  have := congrArg decodeRatCanonical? h
  simpa using this

@[simp] theorem decode_encode_rows (qs : List ℚ) :
    (qs.map encodeRatCanonical).mapM decodeRatCanonical? = some qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [List.mapM_cons, ih]

theorem encode_rows_of_decode {ws : List RatWire} {qs : List ℚ}
    (h : ws.mapM decodeRatCanonical? = some qs) : qs.map encodeRatCanonical = ws := by
  induction ws generalizing qs with
  | nil => simp at h; subst qs; rfl
  | cons w ws ih =>
    cases hd : decodeRatCanonical? w with
    | none => simp [List.mapM_cons, hd] at h
    | some q =>
      cases ht : ws.mapM decodeRatCanonical? with
      | none => simp [List.mapM_cons, hd, ht] at h
      | some tail =>
        simp [List.mapM_cons, hd, ht] at h
        subst qs
        simp [encode_of_decode_rat hd, ih ht]

theorem decode_rows_isSome_iff (ws : List RatWire) :
    (ws.mapM decodeRatCanonical?).isSome = true ↔ ∀ w ∈ ws, CanonicalRatWire w := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    cases hd : decodeRatCanonical? w with
    | none =>
      have hn : ¬ CanonicalRatWire w := by
        rw [← decode_rat_isSome_iff, hd]; simp
      simp [List.mapM_cons, hd, hn]
    | some q =>
      have hc : CanonicalRatWire w := (decode_rat_isSome_iff w).mp (by simp [hd])
      cases ht : ws.mapM decodeRatCanonical? <;>
        simp_all [List.mapM_cons]

/-- Applies to every typed snapshot, regardless of semantic validity or row length. -/
@[simp] theorem decode_encode_snapshot (s : QuotaCursorSnapshot) :
    decodeSnapshotCanonical? (encodeSnapshotCanonical s) = some s := by
  change ((s.row.map encodeRatCanonical).mapM decodeRatCanonical?).bind
    (fun row => some ⟨s.bound, row⟩) = some s
  rw [decode_encode_rows]
  rfl

theorem encode_of_decode_snapshot {w : QuotaSnapshotWire} {s : QuotaCursorSnapshot}
    (h : decodeSnapshotCanonical? w = some s) : encodeSnapshotCanonical s = w := by
  cases hr : w.row.mapM decodeRatCanonical? with
  | none => simp [decodeSnapshotCanonical?, hr] at h
  | some row =>
    have hs : (⟨w.bound, row⟩ : QuotaCursorSnapshot) = s := by
      simpa [decodeSnapshotCanonical?, hr] using h
    rw [← hs]
    have he := encode_rows_of_decode hr
    cases w
    simp_all [encodeSnapshotCanonical]

theorem decode_snapshot_iff (w : QuotaSnapshotWire) (s : QuotaCursorSnapshot) :
    decodeSnapshotCanonical? w = some s ↔ encodeSnapshotCanonical s = w := by
  constructor
  · exact encode_of_decode_snapshot
  · intro h; rw [← h]; exact decode_encode_snapshot s

theorem decode_snapshot_isSome_iff (w : QuotaSnapshotWire) :
    (decodeSnapshotCanonical? w).isSome = true ↔ CanonicalSnapshotWire w := by
  have h := decode_rows_isSome_iff w.row
  cases hr : w.row.mapM decodeRatCanonical? <;>
    simpa [decodeSnapshotCanonical?, CanonicalSnapshotWire, hr] using h

theorem encode_snapshot_injective : Function.Injective encodeSnapshotCanonical := by
  intro s t h
  have := congrArg decodeSnapshotCanonical? h
  simpa using this

theorem decode_preserves_bound {w : QuotaSnapshotWire} {s : QuotaCursorSnapshot}
    (h : decodeSnapshotCanonical? w = some s) : s.bound = w.bound :=
  congrArg QuotaSnapshotWire.bound (encode_of_decode_snapshot h)

theorem decode_preserves_length {w : QuotaSnapshotWire} {s : QuotaCursorSnapshot}
    (h : decodeSnapshotCanonical? w = some s) : s.row.length = w.row.length := by
  have he := congrArg (fun x : QuotaSnapshotWire => x.row.length) (encode_of_decode_snapshot h)
  simpa [encodeSnapshotCanonical] using he

@[simp] theorem restore_encoded_snapshot (n p j ε) (s : QuotaCursorSnapshot) :
    restoreFromExternal? n p j ε (encodeSnapshotCanonical s) = restoreCursor? n p j ε s := by
  simp [restoreFromExternal?]

@[simp] theorem restore_encoded_cursor {n p j ε} (c : QuotaSearchCursor n p j ε) :
    restoreFromExternal? n p j ε (encodeSnapshotCanonical (snapshotCursor c)) = some c := by
  simp [restore_snapshot]

theorem restore_external_iff (n p j ε) (w : QuotaSnapshotWire)
    (c : QuotaSearchCursor n p j ε) :
    restoreFromExternal? n p j ε w = some c ↔
      ∃ s, decodeSnapshotCanonical? w = some s ∧
        ValidSnapshot n p j ε s ∧ snapshotCursor c = s := by
  cases hd : decodeSnapshotCanonical? w with
  | none => simp [restoreFromExternal?, hd]
  | some s =>
    simp only [restoreFromExternal?, hd, Option.bind_some, Option.some.injEq]
    rw [restore_eq_some_iff]
    aesop

theorem restored_resume_correct {n p j ε} (w : QuotaSnapshotWire)
    (c : QuotaSearchCursor n p j ε) (_h : restoreFromExternal? n p j ε w = some c)
    (newCap : ℕ) : ResultCorrect n p j ε newCap (resumeQuotaSearch (.exhausted c) newCap) :=
  resume_exhausted_correct c newCap

theorem restore_resume_eq {n p j ε} (w : QuotaSnapshotWire)
    (c : QuotaSearchCursor n p j ε) (h : restoreFromExternal? n p j ε w = some c)
    (newCap : ℕ) (hb : w.bound ≤ newCap) :
    resumeQuotaSearch (.exhausted c) newCap = startQuotaSearch n p j ε newCap := by
  obtain ⟨s, hd, hv, hs⟩ := (restore_external_iff n p j ε w c).mp h
  apply CryptoHiddenScalarQuotaSnapshotContract.restore_resume_eq s c
  · exact (restore_eq_some_iff s c).mpr ⟨hv, hs⟩
  · simpa [decode_preserves_bound hd] using hb

structure CryptoHiddenScalarQuotaCanonicalWireContractSuite : Prop where
  rational : ∀ w q, decodeRatCanonical? w = some q ↔ encodeRatCanonical q = w
  snapshot : ∀ w s, decodeSnapshotCanonical? w = some s ↔ encodeSnapshotCanonical s = w
  canonical : ∀ w, (decodeSnapshotCanonical? w).isSome = true ↔ CanonicalSnapshotWire w
  round_trip : ∀ s, decodeSnapshotCanonical? (encodeSnapshotCanonical s) = some s
  restore : ∀ n p j ε (c : QuotaSearchCursor n p j ε),
    restoreFromExternal? n p j ε (encodeSnapshotCanonical (snapshotCursor c)) = some c

theorem verification_suite : CryptoHiddenScalarQuotaCanonicalWireContractSuite where
  rational := decode_rat_iff
  snapshot := decode_snapshot_iff
  canonical := decode_snapshot_isSome_iff
  round_trip := decode_encode_snapshot
  restore := fun _ _ _ _ => restore_encoded_cursor
end CryptoHiddenScalarQuotaCanonicalWireContract

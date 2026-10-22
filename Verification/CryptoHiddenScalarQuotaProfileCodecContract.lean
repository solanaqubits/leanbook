/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaCodecContract
import Verification.CryptoHiddenScalarQuotaProfileContract

/-! QCP/01 canonical finite rational profile bytes. Context-free decoding and
independent expected-profile checking are separate. No file IO, provenance,
physical qualification or practical resource-complexity theorem. -/
namespace CryptoHiddenScalarQuotaProfileCodecContract
open CryptoHiddenScalarQuotaCodecContract
  (encodeNat parseNat encodeRows parseRows parseNat_encode_append parseRows_encode_append)
open CryptoHiddenScalarQuotaProfileContract
open CryptoHiddenScalarQuotaSnapshotContract

structure ProfileLimits where
  maxSizeBytes : ℕ
  maxCoefficients : ℕ
  deriving DecidableEq, Repr

/-- ASCII QCP and version 01; distinct from the QCS snapshot format. -/
def magicV1 : List UInt8 := [0x51, 0x43, 0x50, 0x01]

def encodeData (xs : List ℚ) : List UInt8 :=
  magicV1 ++ encodeNat xs.length ++ encodeRows xs

def encodeV1 (xs : List ℚ) : ByteArray := ⟨(encodeData xs).toArray⟩

def Fits (limits : ProfileLimits) (xs : List ℚ) : Prop :=
  xs.length ≤ limits.maxCoefficients ∧ (encodeV1 xs).size ≤ limits.maxSizeBytes

instance (limits xs) : Decidable (Fits limits xs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Check the count before parsing coefficients; require exact end of frame. -/
def parseFrame (limits : ProfileLimits) (bs : List UInt8) : Option (List ℚ) := do
  if bs.take 4 = magicV1 then do
    let (count, body) ← parseNat (bs.drop 4)
    if count ≤ limits.maxCoefficients then do
      let (xs, tail) ← parseRows count body
      if tail = [] then some xs else none
    else none
  else none

/-- Size guard precedes list parsing. Exact re-encoding is a canonicality guard,
not a hash or a source-authentication check. Input bytes are already resident. -/
def strictDecode (limits : ProfileLimits) (bytes : ByteArray) : Option (List ℚ) :=
  if bytes.size ≤ limits.maxSizeBytes then
    match parseFrame limits bytes.data.toList with
    | none => none
    | some xs => if Fits limits xs ∧ encodeV1 xs = bytes then some xs else none
  else none

theorem parseFrame_encode (limits : ProfileLimits) (xs : List ℚ)
    (h : xs.length ≤ limits.maxCoefficients) :
    parseFrame limits (encodeData xs) = some xs := by
  simp only [parseFrame, encodeData, magicV1, List.cons_append,
    List.nil_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, ↓reduceIte]
  rw [parseNat_encode_append]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [if_pos h]
  have hp := parseRows_encode_append xs []
  simp only [List.append_nil] at hp
  rw [hp]
  simp

theorem decode_encodeV1 (limits : ProfileLimits) (xs : List ℚ) (h : Fits limits xs) :
    strictDecode limits (encodeV1 xs) = some xs := by
  unfold strictDecode
  rw [if_pos h.2]
  have hb : (encodeV1 xs).data.toList = encodeData xs := by simp [encodeV1]
  rw [hb, parseFrame_encode limits xs h.1]
  simp [h]

theorem decode_canonical (limits : ProfileLimits) (bytes : ByteArray)
    (xs : List ℚ) (h : strictDecode limits bytes = some xs) :
    Fits limits xs ∧ encodeV1 xs = bytes := by
  unfold strictDecode at h
  split at h
  next =>
    cases hp : parseFrame limits bytes.data.toList with
    | none => simp [hp] at h
    | some ys =>
      simp only [hp] at h
      split at h
      next hy =>
        have he : ys = xs := Option.some.inj h
        simpa only [he] using hy
      next => simp at h
  next => simp at h

theorem decode_iff (limits bytes xs) :
    strictDecode limits bytes = some xs ↔ Fits limits xs ∧ encodeV1 xs = bytes := by
  constructor
  · exact decode_canonical limits bytes xs
  · rintro ⟨hf, he⟩
    rw [← he]
    exact decode_encodeV1 limits xs hf

theorem encodeV1_size_pos (xs : List ℚ) : 0 < (encodeV1 xs).size := by
  simp [encodeV1, encodeData, magicV1, ByteArray.size]

theorem zero_size_refuses (limits : ProfileLimits) (h : limits.maxSizeBytes = 0)
    (bytes : ByteArray) : strictDecode limits bytes = none := by
  cases he : strictDecode limits bytes with
  | none => rfl
  | some xs =>
    have hf := (decode_canonical limits bytes xs he).1.2
    have hp := encodeV1_size_pos xs
    omega

theorem encodeV1_injective : Function.Injective encodeV1 := by
  intro xs ys he
  let limits : ProfileLimits :=
    ⟨max (encodeV1 xs).size (encodeV1 ys).size, max xs.length ys.length⟩
  have hx : Fits limits xs := ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩
  have hy : Fits limits ys := ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
  have h₁ := decode_encodeV1 limits xs hx
  have h₂ := decode_encodeV1 limits ys hy
  rw [he, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-- n and expected are external; neither is read from the byte frame. -/
def decodeExpected? (limits : ProfileLimits) (n : ℕ) (expected : ℕ → ℚ)
    (bytes : ByteArray) : Option (List ℚ) := do
  let xs ← strictDecode limits bytes
  if Matches n expected xs then some xs else none

theorem decodeExpected_iff (limits n expected bytes xs) :
    decodeExpected? limits n expected bytes = some xs ↔
      Fits limits xs ∧ encodeV1 xs = bytes ∧ Matches n expected xs := by
  unfold decodeExpected?
  simp only [Option.bind_eq_bind]
  cases hd : strictDecode limits bytes with
  | none =>
    simp only [Option.bind_none]
    constructor
    · intro h; cases h
    · rintro ⟨hf, he, _⟩
      have h := (decode_iff limits bytes xs).mpr ⟨hf, he⟩
      simp [hd] at h
  | some ys =>
    simp only [Option.bind_some]
    constructor
    · intro h
      split at h
      next hm =>
        have he : ys = xs := Option.some.inj h
        subst ys
        exact ⟨(decode_canonical limits bytes xs hd).1,
          (decode_canonical limits bytes xs hd).2, hm⟩
      next => simp at h
    · rintro ⟨hf, he, hm⟩
      have hs := (decode_iff limits bytes xs).mpr ⟨hf, he⟩
      have hy : ys = xs := Option.some.inj (hd.symm.trans hs)
      subst ys
      simp [hm]

/-- Only the existing typed transfer/restoration builds a certified cursor.
Return its exact snapshot; no authorization follows from this projection. -/
def restoreProfileBytes? (limits : ProfileLimits) (n : ℕ) (expected : ℕ → ℚ)
    (j : ℕ) (ε : ℚ) (bytes : ByteArray) (s : QuotaCursorSnapshot) :
    Option QuotaCursorSnapshot := do
  let xs ← decodeExpected? limits n expected bytes
  let c ← restoreTransferred? n expected j ε xs s
  some (snapshotCursor c)

theorem restoreProfileBytes_iff (limits n expected j ε bytes s out) :
    restoreProfileBytes? limits n expected j ε bytes s = some out ↔
      Fits limits (exportProfile n expected) ∧
      encodeV1 (exportProfile n expected) = bytes ∧
      ValidSnapshot n expected j ε s ∧ out = s := by
  unfold restoreProfileBytes?
  simp only [Option.bind_eq_bind]
  cases hd : decodeExpected? limits n expected bytes with
  | none =>
    simp only [Option.bind_none]
    constructor
    · intro h; cases h
    · rintro ⟨hf, he, _, _⟩
      have h := (decodeExpected_iff limits n expected bytes (exportProfile n expected)).mpr
        ⟨hf, he, export_matches n expected⟩
      simp [hd] at h
  | some xs =>
    have hx := (decodeExpected_iff limits n expected bytes xs).mp hd
    have he := (matches_iff n expected xs).mp hx.2.2
    subst xs
    simp only [Option.bind_some]
    have hm := Option.map_eq_bind (f := fun c => snapshotCursor c)
      (x := restoreTransferred? n expected j ε (exportProfile n expected) s)
    simp only [Function.comp_def] at hm
    rw [← hm]
    rw [transferred_export, restore_projection]
    by_cases hv : ValidSnapshot n expected j ε s
    · simp [hv, hx.1, hx.2.1, eq_comm]
    · simp [hv]

structure CryptoHiddenScalarQuotaProfileCodecContractSuite : Prop where
  round_trip : ∀ limits xs, Fits limits xs → strictDecode limits (encodeV1 xs) = some xs
  canonical : ∀ limits bytes xs, strictDecode limits bytes = some xs →
    Fits limits xs ∧ encodeV1 xs = bytes
  injective : Function.Injective encodeV1
  expected : ∀ limits n p bytes xs, decodeExpected? limits n p bytes = some xs ↔
    Fits limits xs ∧ encodeV1 xs = bytes ∧ Matches n p xs
  restore : ∀ limits n p j ε bytes s out,
    restoreProfileBytes? limits n p j ε bytes s = some out ↔
      Fits limits (exportProfile n p) ∧ encodeV1 (exportProfile n p) = bytes ∧
      ValidSnapshot n p j ε s ∧ out = s

theorem verification_suite : CryptoHiddenScalarQuotaProfileCodecContractSuite where
  round_trip := decode_encodeV1
  canonical := decode_canonical
  injective := encodeV1_injective
  expected := decodeExpected_iff
  restore := restoreProfileBytes_iff
end CryptoHiddenScalarQuotaProfileCodecContract

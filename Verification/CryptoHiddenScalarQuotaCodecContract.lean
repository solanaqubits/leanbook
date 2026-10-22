/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaSnapshotContract

/-! Canonical QCS version 1. Typed ByteArray codec, not a file reader, resource
cost proof, profile transport, provenance check or authorization mechanism. -/
namespace CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaSnapshotContract

structure FitsLimits where
  maxSizeBytes : ℕ
  maxBound : ℕ
  maxRowLength : ℕ
  deriving DecidableEq, Repr

/-- Minimal unsigned base-128 groups, low group first. -/
def encodeNat (n : ℕ) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 128 + 128) :: encodeNat (n / 128)
termination_by n

def parseNat : List UInt8 → Option (ℕ × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else do
      let (n, rest) ← parseNat bs
      if n = 0 then none else some (b.toNat - 128 + 128 * n, rest)

/-- Prefix parser round trip, with arbitrary uninterpreted suffix. -/
theorem parseNat_encode_append (n : ℕ) (tail : List UInt8) :
    parseNat (encodeNat n ++ tail) = some (n, tail) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [encodeNat]
    split_ifs with hn
    · have hb : (UInt8.ofNat n).toNat = n := UInt8.toNat_ofNat_of_lt' (by change n < 256; omega)
      simp [parseNat, hb, hn]
    · have hmod : n % 128 < 128 := Nat.mod_lt n (by decide)
      have hb : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 :=
        UInt8.toNat_ofNat_of_lt' (by change n % 128 + 128 < 256; omega)
      have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by decide)
      have hnz : n / 128 ≠ 0 := by omega
      simp only [List.cons_append, parseNat, hb]
      rw [if_neg (by omega), ih (n / 128) hlt]
      simp only [Option.bind_eq_bind, Option.bind_some, hnz, ↓reduceIte]
      congr 2
      omega

def signByte (num : ℤ) : UInt8 := if num < 0 then 1 else 0

def signedNum (sign : UInt8) (mag : ℕ) : ℤ :=
  if sign = 1 then -(mag : ℤ) else (mag : ℤ)

theorem signedNum_signByte (num : ℤ) : signedNum (signByte num) num.natAbs = num := by
  by_cases h : num < 0
  · simp [signByte, signedNum, h, Int.ofNat_natAbs_of_nonpos (by omega : num ≤ 0)]
  · simp [signByte, signedNum, h, Int.ofNat_natAbs_of_nonneg (by omega : 0 ≤ num)]

def encodeRat (q : ℚ) : List UInt8 :=
  signByte q.num :: (encodeNat q.num.natAbs ++ encodeNat q.den)

def parseRat : List UInt8 → Option (ℚ × List UInt8)
  | [] => none
  | sign :: bs =>
    if sign = 0 ∨ sign = 1 then do
      let (mag, rest) ← parseNat bs
      let (den, tail) ← parseNat rest
      if den ≠ 0 ∧ mag.Coprime den ∧ (sign = 1 → mag ≠ 0) then
        some (mkRat (signedNum sign mag) den, tail)
      else none
    else none

theorem parseRat_encode_append (q : ℚ) (tail : List UInt8) :
    parseRat (encodeRat q ++ tail) = some (q, tail) := by
  have hs : signByte q.num = 0 ∨ signByte q.num = 1 := by
    unfold signByte
    split_ifs <;> simp
  have hz : signByte q.num = 1 → q.num.natAbs ≠ 0 := by
    unfold signByte
    split_ifs with h
    · intro _ hh
      have : q.num = 0 := Int.natAbs_eq_zero.mp hh
      omega
    · simp
  simp only [encodeRat, List.cons_append, List.append_assoc, parseRat, hs, ↓reduceIte]
  rw [parseNat_encode_append]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [parseNat_encode_append]
  simp only [Option.bind_some]
  rw [if_pos ⟨q.den_nz, q.reduced, hz⟩, signedNum_signByte, Rat.mkRat_self]

def encodeRows : List ℚ → List UInt8
  | [] => []
  | q :: qs => encodeRat q ++ encodeRows qs

/-- No allocation based on an unvalidated count. The caller bounds the count;
each step parses one rational before constructing its list cell. -/
def parseRows : ℕ → List UInt8 → Option (List ℚ × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (q, rest) ← parseRat bs
    let (qs, tail) ← parseRows n rest
    some (q :: qs, tail)

theorem parseRows_encode_append (qs : List ℚ) (tail : List UInt8) :
    parseRows qs.length (encodeRows qs ++ tail) = some (qs, tail) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp [encodeRows, List.append_assoc, parseRows, parseRat_encode_append, ih]

/-- ASCII QCS followed by the version byte 01. -/
def magicV1 : List UInt8 := [0x51, 0x43, 0x53, 0x01]

def encodeData (s : QuotaCursorSnapshot) : List UInt8 :=
  magicV1 ++ encodeNat s.bound ++ encodeNat s.row.length ++ encodeRows s.row

def encodeV1 (s : QuotaCursorSnapshot) : ByteArray := ⟨(encodeData s).toArray⟩

def Fits (limits : FitsLimits) (s : QuotaCursorSnapshot) : Prop :=
  s.bound ≤ limits.maxBound ∧ s.row.length ≤ limits.maxRowLength ∧
    (encodeV1 s).size ≤ limits.maxSizeBytes

instance (limits : FitsLimits) (s : QuotaCursorSnapshot) : Decidable (Fits limits s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Bound and count guards precede parsing/constructing the row. -/
def parseFrame (limits : FitsLimits) (bs : List UInt8) : Option QuotaCursorSnapshot := do
  if bs.take 4 = magicV1 then do
    let (bound, rest) ← parseNat (bs.drop 4)
    if bound ≤ limits.maxBound then do
      let (count, rows) ← parseNat rest
      if count ≤ limits.maxRowLength then do
        let (row, tail) ← parseRows count rows
        if tail = [] then some ⟨bound, row⟩ else none
      else none
    else none
  else none

/-- Structural decoding only; caller supplies a bounded, already-read ByteArray.
The last exact byte comparison is a deliberate canonicality check, not a hash. -/
def strictDecode (limits : FitsLimits) (bytes : ByteArray) : Option QuotaCursorSnapshot :=
  if bytes.size ≤ limits.maxSizeBytes then
    match parseFrame limits bytes.data.toList with
    | none => none
    | some s => if Fits limits s ∧ encodeV1 s = bytes then some s else none
  else none

theorem parseFrame_encode (limits : FitsLimits) (s : QuotaCursorSnapshot)
    (hb : s.bound ≤ limits.maxBound) (hr : s.row.length ≤ limits.maxRowLength) :
    parseFrame limits (encodeData s) = some s := by
  simp only [parseFrame, encodeData, magicV1, List.append_assoc, List.cons_append,
    List.nil_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, ↓reduceIte]
  rw [parseNat_encode_append]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [if_pos hb, parseNat_encode_append]
  simp only [Option.bind_some]
  rw [if_pos hr]
  have hp := parseRows_encode_append s.row []
  simp only [List.append_nil] at hp
  rw [hp]
  simp

theorem decode_encodeV1 (limits : FitsLimits) (s : QuotaCursorSnapshot)
    (h : Fits limits s) : strictDecode limits (encodeV1 s) = some s := by
  unfold strictDecode
  rw [if_pos h.2.2]
  have hb : (encodeV1 s).data.toList = encodeData s := by simp [encodeV1]
  rw [hb, parseFrame_encode limits s h.1 h.2.1]
  simp [h]

theorem decode_canonical (limits : FitsLimits) (bytes : ByteArray)
    (s : QuotaCursorSnapshot) (h : strictDecode limits bytes = some s) :
    Fits limits s ∧ encodeV1 s = bytes := by
  unfold strictDecode at h
  split at h
  next hsize =>
    cases hp : parseFrame limits bytes.data.toList with
    | none => simp [hp] at h
    | some t =>
      simp only [hp] at h
      split at h
      next ht =>
        have he : t = s := Option.some.inj h
        simpa only [he] using ht
      next ht => simp at h
  next hsize => simp at h

theorem decode_iff (limits : FitsLimits) (bytes : ByteArray) (s : QuotaCursorSnapshot) :
    strictDecode limits bytes = some s ↔ Fits limits s ∧ encodeV1 s = bytes := by
  constructor
  · exact decode_canonical limits bytes s
  · rintro ⟨hf, he⟩
    rw [← he]
    exact decode_encodeV1 limits s hf

theorem encodeV1_size_pos (s : QuotaCursorSnapshot) : 0 < (encodeV1 s).size := by
  simp [encodeV1, encodeData, magicV1, ByteArray.size]

theorem zero_size_refuses (limits : FitsLimits) (h : limits.maxSizeBytes = 0)
    (bytes : ByteArray) : strictDecode limits bytes = none := by
  cases he : strictDecode limits bytes with
  | none => rfl
  | some s =>
    have hf := (decode_canonical limits bytes s he).1.2.2
    have hp := encodeV1_size_pos s
    omega

/-- Canonical encoding is injective even without a common preselected limit. -/
theorem encodeV1_injective : Function.Injective encodeV1 := by
  intro s t he
  let limits : FitsLimits :=
    ⟨max (encodeV1 s).size (encodeV1 t).size,
      max s.bound t.bound, max s.row.length t.row.length⟩
  have hs : Fits limits s :=
    ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩
  have ht : Fits limits t :=
    ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩
  have h₁ := decode_encodeV1 limits s hs
  have h₂ := decode_encodeV1 limits t ht
  rw [he, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-- A fixed input and limits have at most one decoded snapshot. -/
theorem decode_unique (limits : FitsLimits) (bytes : ByteArray)
    (s t : QuotaCursorSnapshot) (hs : strictDecode limits bytes = some s)
    (ht : strictDecode limits bytes = some t) : s = t :=
  Option.some.inj (hs.symm.trans ht)

structure CryptoHiddenScalarQuotaCodecContractSuite : Prop where
  round_trip : ∀ limits s, Fits limits s → strictDecode limits (encodeV1 s) = some s
  canonical : ∀ limits bytes s, strictDecode limits bytes = some s →
    Fits limits s ∧ encodeV1 s = bytes
  injective : Function.Injective encodeV1
  zero_size : ∀ limits, limits.maxSizeBytes = 0 → ∀ bytes, strictDecode limits bytes = none

theorem verification_suite : CryptoHiddenScalarQuotaCodecContractSuite where
  round_trip := decode_encodeV1
  canonical := decode_canonical
  injective := encodeV1_injective
  zero_size := zero_size_refuses
end CryptoHiddenScalarQuotaCodecContract

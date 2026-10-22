/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarQuotaCodecContract

/-! Canonical manifest representation only. No SHA implementation, signature
verification, external trust, freshness or replay-state mutation is provided. -/
namespace DigitalProvenanceManifestContract
open CryptoHiddenScalarQuotaCodecContract
  (encodeNat parseNat encodeRat parseRat signByte signedNum
   parseNat_encode_append parseRat_encode_append signedNum_signByte)

structure Digest256 where
  bytes : ByteArray
  size_eq : bytes.size = 32
  deriving DecidableEq

structure ArtifactBinding where
  sizeBytes : Nat
  digest : Digest256
  deriving DecidableEq

structure TimeClaim where
  scaleId : String
  unitId : String
  value : Int
  deriving DecidableEq

structure ProvenanceManifestV1 where
  signerId : String
  keyId : String
  roleId : String
  sessionId : String
  challenge : ByteArray
  policyVersion : String
  snapshot : ArtifactBinding
  profile : ArtifactBinding
  n : Nat
  j : Nat
  epsilon : ℚ
  expectedContextId : String
  claimedTime : Option TimeClaim
  deriving DecidableEq

structure SignedProvenanceV1 where
  manifest : ProvenanceManifestV1
  signature : ByteArray

inductive AuthorizationStatus where
  | blocked
  deriving DecidableEq

structure ManifestLimits where
  maxManifestSizeBytes : Nat
  maxStringBytes : Nat
  maxChallengeBytes : Nat
  deriving DecidableEq

def encodeBytes (bs : ByteArray) : List UInt8 := encodeNat bs.size ++ bs.data.toList

def parseBytes (limit : Nat) (bs : List UInt8) : Option (ByteArray × List UInt8) := do
  let (len, rest) ← parseNat bs
  if len ≤ limit ∧ len ≤ rest.length then
    some (⟨(rest.take len).toArray⟩, rest.drop len)
  else none

theorem parseBytes_encode_append (bs : ByteArray) (tail : List UInt8) (limit : Nat)
    (h : bs.size ≤ limit) :
    parseBytes limit (encodeBytes bs ++ tail) = some (bs, tail) := by
  simp only [parseBytes, encodeBytes, List.append_assoc, parseNat_encode_append,
    Option.bind_eq_bind, Option.bind_some]
  have hb : bs.size = bs.data.toList.length := by simp only [ByteArray.size, Array.length_toList]
  have hr : bs.size ≤ (bs.data.toList ++ tail).length := by
    simp only [List.length_append, ← hb]; omega
  rw [if_pos ⟨h, hr⟩]
  simp only [hb, List.take_left, List.drop_left, Array.toArray_toList]

/-- UTF-8 is exact, without Unicode normalization or case folding. -/
def encodeString (s : String) : List UInt8 := encodeBytes s.toUTF8

def parseString (limit : Nat) (bs : List UInt8) : Option (String × List UInt8) := do
  let (raw, tail) ← parseBytes limit bs
  let s ← String.fromUTF8? raw
  some (s, tail)

theorem utf8_roundTrip (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.toUTF8 String.fromUTF8?
  rw [dif_pos s.isValidUTF8]
  rfl

theorem parseString_encode_append (s : String) (tail : List UInt8) (limit : Nat)
    (h : s.toUTF8.size ≤ limit) :
    parseString limit (encodeString s ++ tail) = some (s, tail) := by
  simp only [parseString, encodeString, parseBytes_encode_append _ _ _ h,
    Option.bind_eq_bind, Option.bind_some, utf8_roundTrip]

/-- Sign byte followed by minimal ULEB128 magnitude; negative zero is rejected. -/
def encodeInt (z : Int) : List UInt8 := signByte z :: encodeNat z.natAbs

def parseInt : List UInt8 → Option (Int × List UInt8)
  | [] => none
  | sign :: bs => do
    if sign = 0 ∨ sign = 1 then
      let (mag, tail) ← parseNat bs
      if sign = 1 → mag ≠ 0 then some (signedNum sign mag, tail) else none
    else none

theorem parseInt_encode_append (z : Int) (tail : List UInt8) :
    parseInt (encodeInt z ++ tail) = some (z, tail) := by
  have hs : signByte z = 0 ∨ signByte z = 1 := by
    unfold signByte; split_ifs <;> simp
  have hz : signByte z = 1 → z.natAbs ≠ 0 := by
    unfold signByte
    split_ifs with h
    · intro _ hh
      have : z = 0 := Int.natAbs_eq_zero.mp hh
      omega
    · simp
  simp only [encodeInt, List.cons_append, parseInt, hs, ↓reduceIte,
    parseNat_encode_append, Option.bind_eq_bind, Option.bind_some]
  rw [if_pos hz, signedNum_signByte]

def encodeDigest (d : Digest256) : List UInt8 := encodeBytes d.bytes

def parseDigest (bs : List UInt8) : Option (Digest256 × List UInt8) := do
  let (raw, tail) ← parseBytes 32 bs
  if h : raw.size = 32 then some (⟨raw, h⟩, tail) else none

theorem parseDigest_encode_append (d : Digest256) (tail : List UInt8) :
    parseDigest (encodeDigest d ++ tail) = some (d, tail) := by
  simp [parseDigest, encodeDigest, parseBytes_encode_append _ _ _ (Nat.le_of_eq d.size_eq),
    d.size_eq]

def encodeBinding (b : ArtifactBinding) : List UInt8 :=
  encodeNat b.sizeBytes ++ encodeDigest b.digest

def parseBinding (bs : List UInt8) : Option (ArtifactBinding × List UInt8) := do
  let (size, rest) ← parseNat bs
  let (digest, tail) ← parseDigest rest
  some (⟨size, digest⟩, tail)

theorem parseBinding_encode_append (b : ArtifactBinding) (tail : List UInt8) :
    parseBinding (encodeBinding b ++ tail) = some (b, tail) := by
  simp [parseBinding, encodeBinding, List.append_assoc, parseNat_encode_append,
    parseDigest_encode_append]

def encodeTime (t : Option TimeClaim) : List UInt8 :=
  match t with
  | none => [0]
  | some t => 1 :: (encodeString t.scaleId ++ encodeString t.unitId ++ encodeInt t.value)

def parseTime (limit : Nat) : List UInt8 → Option (Option TimeClaim × List UInt8)
  | [] => none
  | tag :: bs =>
    if tag = 0 then some (none, bs)
    else if tag = 1 then do
      let (scale, rest) ← parseString limit bs
      let (unit, rest) ← parseString limit rest
      let (value, tail) ← parseInt rest
      some (some ⟨scale, unit, value⟩, tail)
    else none

def TimeFits (limit : Nat) : Option TimeClaim → Prop
  | none => True
  | some t => t.scaleId.toUTF8.size ≤ limit ∧ t.unitId.toUTF8.size ≤ limit

instance (limit t) : Decidable (TimeFits limit t) := by
  cases t <;> unfold TimeFits <;> infer_instance

theorem parseTime_encode_append (t : Option TimeClaim) (tail : List UInt8) (limit : Nat)
    (h : TimeFits limit t) : parseTime limit (encodeTime t ++ tail) = some (t, tail) := by
  cases t with
  | none => simp [encodeTime, parseTime]
  | some t =>
    simp [encodeTime, parseTime, List.append_assoc,
      parseString_encode_append _ _ _ h.1, parseString_encode_append _ _ _ h.2,
      parseInt_encode_append]


def timeStringLimit : Option TimeClaim → Nat
  | none => 0
  | some t => max t.scaleId.toUTF8.size t.unitId.toUTF8.size

theorem timeFits_iff (limit t) : TimeFits limit t ↔ timeStringLimit t ≤ limit := by
  cases t <;> simp [TimeFits, timeStringLimit]

def requiredStringLimit (m : ProvenanceManifestV1) : Nat :=
  max m.signerId.toUTF8.size (max m.keyId.toUTF8.size
    (max m.roleId.toUTF8.size (max m.sessionId.toUTF8.size
      (max m.policyVersion.toUTF8.size (max m.expectedContextId.toUTF8.size
        (timeStringLimit m.claimedTime))))))

def encodeBody (m : ProvenanceManifestV1) : List UInt8 :=
  encodeString m.signerId ++ encodeString m.keyId ++ encodeString m.roleId ++
  encodeString m.sessionId ++ encodeBytes m.challenge ++ encodeString m.policyVersion ++
  encodeBinding m.snapshot ++ encodeBinding m.profile ++ encodeNat m.n ++ encodeNat m.j ++
  encodeRat m.epsilon ++ encodeString m.expectedContextId ++ encodeTime m.claimedTime

def parseBody (limits : ManifestLimits) (bs : List UInt8) :
    Option (ProvenanceManifestV1 × List UInt8) := do
  let (signerId, bs) ← parseString limits.maxStringBytes bs
  let (keyId, bs) ← parseString limits.maxStringBytes bs
  let (roleId, bs) ← parseString limits.maxStringBytes bs
  let (sessionId, bs) ← parseString limits.maxStringBytes bs
  let (challenge, bs) ← parseBytes limits.maxChallengeBytes bs
  let (policyVersion, bs) ← parseString limits.maxStringBytes bs
  let (snapshot, bs) ← parseBinding bs
  let (profile, bs) ← parseBinding bs
  let (n, bs) ← parseNat bs
  let (j, bs) ← parseNat bs
  let (epsilon, bs) ← parseRat bs
  let (expectedContextId, bs) ← parseString limits.maxStringBytes bs
  let (claimedTime, bs) ← parseTime limits.maxStringBytes bs
  some (⟨signerId, keyId, roleId, sessionId, challenge, policyVersion,
    snapshot, profile, n, j, epsilon, expectedContextId, claimedTime⟩, bs)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Normalizing thirteen nested parser binds exceeds the default elaboration budget.
theorem parseBody_encode_append (limits : ManifestLimits) (m : ProvenanceManifestV1)
    (tail : List UInt8) (hs : requiredStringLimit m ≤ limits.maxStringBytes)
    (hc : m.challenge.size ≤ limits.maxChallengeBytes) :
    parseBody limits (encodeBody m ++ tail) = some (m, tail) := by
  simp only [requiredStringLimit, Nat.max_le] at hs
  have ht := (timeFits_iff _ _).mpr hs.2.2.2.2.2.2
  simp only [encodeBody, List.append_assoc, parseBody]
  rw [parseString_encode_append _ _ _ hs.1]
  simp (config := { maxSteps := 1000000 }) only [Option.bind_eq_bind, Option.bind_some]
  rw [parseString_encode_append _ _ _ hs.2.1]
  simp only [Option.bind_some]
  rw [parseString_encode_append _ _ _ hs.2.2.1]
  simp only [Option.bind_some]
  rw [parseString_encode_append _ _ _ hs.2.2.2.1]
  simp only [Option.bind_some]
  rw [parseBytes_encode_append _ _ _ hc]
  simp only [Option.bind_some]
  rw [parseString_encode_append _ _ _ hs.2.2.2.2.1]
  simp only [Option.bind_some]
  rw [parseBinding_encode_append]
  simp only [Option.bind_some]
  rw [parseBinding_encode_append]
  simp only [Option.bind_some]
  rw [parseNat_encode_append]
  simp only [Option.bind_some]
  rw [parseNat_encode_append]
  simp only [Option.bind_some]
  rw [parseRat_encode_append]
  simp only [Option.bind_some]
  rw [parseString_encode_append _ _ _ hs.2.2.2.2.2.1]
  simp only [Option.bind_some]
  rw [parseTime_encode_append _ _ _ ht]
  simp only [Option.bind_some]

/-- ASCII QPM followed by version 01. The signature is outside this frame. -/
def magicV1 : List UInt8 := [0x51, 0x50, 0x4d, 0x01]
def encodeData (m : ProvenanceManifestV1) : List UInt8 := magicV1 ++ encodeBody m
def encodeManifestV1 (m : ProvenanceManifestV1) : ByteArray := ⟨(encodeData m).toArray⟩

def FitsManifestLimits (limits : ManifestLimits) (m : ProvenanceManifestV1) : Prop :=
  requiredStringLimit m ≤ limits.maxStringBytes ∧
  m.challenge.size ≤ limits.maxChallengeBytes ∧
  (encodeManifestV1 m).size ≤ limits.maxManifestSizeBytes

instance (limits m) : Decidable (FitsManifestLimits limits m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def parseFrame (limits : ManifestLimits) (bs : List UInt8) : Option ProvenanceManifestV1 := do
  if bs.take 4 = magicV1 then
    let (m, tail) ← parseBody limits (bs.drop 4)
    if tail = [] then some m else none
  else none

/-- Input is already resident. Total size is checked before list conversion.
The final byte comparison enforces canonicality, not cryptographic authenticity. -/
def strictDecodeManifest (limits : ManifestLimits) (bytes : ByteArray) :
    Option ProvenanceManifestV1 :=
  if bytes.size ≤ limits.maxManifestSizeBytes then
    match parseFrame limits bytes.data.toList with
    | none => none
    | some m => if FitsManifestLimits limits m ∧ encodeManifestV1 m = bytes
      then some m else none
  else none

theorem parseFrame_encode (limits : ManifestLimits) (m : ProvenanceManifestV1)
    (hs : requiredStringLimit m ≤ limits.maxStringBytes)
    (hc : m.challenge.size ≤ limits.maxChallengeBytes) :
    parseFrame limits (encodeData m) = some m := by
  simp only [parseFrame, encodeData, magicV1, List.cons_append,
    List.nil_append, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, ↓reduceIte]
  have hp := parseBody_encode_append limits m [] hs hc
  simp only [List.append_nil] at hp
  rw [hp]
  simp

theorem decode_encodeManifestV1 (limits : ManifestLimits) (m : ProvenanceManifestV1)
    (h : FitsManifestLimits limits m) :
    strictDecodeManifest limits (encodeManifestV1 m) = some m := by
  unfold strictDecodeManifest
  rw [if_pos h.2.2]
  have hb : (encodeManifestV1 m).data.toList = encodeData m := by simp [encodeManifestV1]
  rw [hb, parseFrame_encode limits m h.1 h.2.1]
  simp [h]

theorem decodeManifest_canonical (limits : ManifestLimits) (bytes : ByteArray)
    (m : ProvenanceManifestV1) (h : strictDecodeManifest limits bytes = some m) :
    FitsManifestLimits limits m ∧ encodeManifestV1 m = bytes := by
  unfold strictDecodeManifest at h
  split at h
  next =>
    cases hp : parseFrame limits bytes.data.toList with
    | none => simp [hp] at h
    | some out =>
      simp only [hp] at h
      split at h
      next hf =>
        have he : out = m := Option.some.inj h
        simpa only [he] using hf
      next => simp at h
  next => simp at h

theorem decodeManifest_iff (limits bytes m) :
    strictDecodeManifest limits bytes = some m ↔
      FitsManifestLimits limits m ∧ encodeManifestV1 m = bytes := by
  constructor
  · exact decodeManifest_canonical limits bytes m
  · rintro ⟨hf, he⟩
    rw [← he]
    exact decode_encodeManifestV1 limits m hf

theorem encodeManifestV1_injective : Function.Injective encodeManifestV1 := by
  intro m₁ m₂ he
  let limits : ManifestLimits :=
    ⟨max (encodeManifestV1 m₁).size (encodeManifestV1 m₂).size,
      max (requiredStringLimit m₁) (requiredStringLimit m₂),
      max m₁.challenge.size m₂.challenge.size⟩
  have h₁ : FitsManifestLimits limits m₁ :=
    ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩
  have h₂ : FitsManifestLimits limits m₂ :=
    ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩
  have hx := decode_encodeManifestV1 limits m₁ h₁
  have hy := decode_encodeManifestV1 limits m₂ h₂
  rw [he, hy] at hx
  exact (Option.some.inj hx).symm

/-- Added exactly once. No application prehash is performed. -/
def domainPrefixV1 : ByteArray := "SIMLAB_PROVENANCE_V1_SHA256_ED25519:".toUTF8
def signingMessageV1 (m : ProvenanceManifestV1) : ByteArray :=
  domainPrefixV1 ++ encodeManifestV1 m

theorem signingMessageV1_injective : Function.Injective signingMessageV1 := by
  intro m₁ m₂ he
  apply encodeManifestV1_injective
  have hx := congrArg (fun b : ByteArray => b.data.toList) he
  change (domainPrefixV1.data.toList ++ (encodeManifestV1 m₁).data.toList) =
    (domainPrefixV1.data.toList ++ (encodeManifestV1 m₂).data.toList) at hx
  exact ByteArray.ext (Array.toList_inj.mp (List.append_cancel_left hx))

structure DigitalProvenanceManifestContractSuite : Prop where
  round_trip : ∀ limits m, FitsManifestLimits limits m →
    strictDecodeManifest limits (encodeManifestV1 m) = some m
  canonical : ∀ limits bytes m, strictDecodeManifest limits bytes = some m →
    FitsManifestLimits limits m ∧ encodeManifestV1 m = bytes
  injective : Function.Injective encodeManifestV1
  signing_injective : Function.Injective signingMessageV1

theorem verification_suite : DigitalProvenanceManifestContractSuite where
  round_trip := decode_encodeManifestV1
  canonical := decodeManifest_canonical
  injective := encodeManifestV1_injective
  signing_injective := signingMessageV1_injective
end DigitalProvenanceManifestContract

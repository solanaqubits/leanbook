/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DigitalProvenanceManifestContract

/-! Pure verification relative to explicit cryptographic and policy callbacks.
No implementation or security theorem for SHA-256/Ed25519, trusted clock,
key distribution, authorization, or atomic replay registry is supplied. -/
namespace DigitalProvenanceVerificationContract
open DigitalProvenanceManifestContract

/-- Implementations must separately establish their cryptographic conformance. -/
structure CryptoBackend where
  sha256 : ByteArray → Digest256
  verifyEd25519 : ByteArray → ByteArray → ByteArray → Bool

/-- The expected context is supplied independently of the received manifest. -/
structure ExpectedContext where
  signerId : String
  keyId : String
  roleId : String
  sessionId : String
  challenge : ByteArray
  policyVersion : String
  n : Nat
  j : Nat
  epsilon : ℚ
  expectedContextId : String
  deriving DecidableEq

def manifestContext (m : ProvenanceManifestV1) : ExpectedContext :=
  ⟨m.signerId, m.keyId, m.roleId, m.sessionId, m.challenge, m.policyVersion,
    m.n, m.j, m.epsilon, m.expectedContextId⟩

/-- A snapshot of external policy, not a proof that the registry or clock is trusted. -/
structure VerificationPolicy where
  lookupKey : String → String → Option ByteArray
  revoked : String → String → Bool
  acceptsTime : Option TimeClaim → Bool

def BindingMatches (backend : CryptoBackend) (bytes : ByteArray)
    (binding : ArtifactBinding) : Prop :=
  bytes.size = binding.sizeBytes ∧ backend.sha256 bytes = binding.digest

instance (backend bytes binding) : Decidable (BindingMatches backend bytes binding) := by
  unfold BindingMatches; infer_instance

def KeyChecks (backend : CryptoBackend) (policy : VerificationPolicy)
    (snapshot profile signature key : ByteArray) (m : ProvenanceManifestV1) : Prop :=
  key.size = 32 ∧ signature.size = 64 ∧
  policy.revoked m.signerId m.keyId = false ∧ policy.acceptsTime m.claimedTime = true ∧
  BindingMatches backend snapshot m.snapshot ∧ BindingMatches backend profile m.profile ∧
  backend.verifyEd25519 key (signingMessageV1 m) signature = true

instance (backend policy snapshot profile signature key m) :
    Decidable (KeyChecks backend policy snapshot profile signature key m) := by
  unfold KeyChecks; infer_instance

/-- Acceptance is relative to the supplied backend, key policy and expected context. -/
def ManifestAccepted (backend : CryptoBackend) (policy : VerificationPolicy)
    (expected : ExpectedContext) (snapshot profile signature : ByteArray)
    (m : ProvenanceManifestV1) : Prop :=
  manifestContext m = expected ∧ ∃ key,
    policy.lookupKey m.signerId m.keyId = some key ∧
    KeyChecks backend policy snapshot profile signature key m

def checkManifest (backend : CryptoBackend) (policy : VerificationPolicy)
    (expected : ExpectedContext) (snapshot profile signature : ByteArray)
    (m : ProvenanceManifestV1) : Bool :=
  if manifestContext m = expected then
    match policy.lookupKey m.signerId m.keyId with
    | none => false
    | some key => decide (KeyChecks backend policy snapshot profile signature key m)
  else false

theorem checkManifest_iff (backend policy expected snapshot profile signature m) :
    checkManifest backend policy expected snapshot profile signature m = true ↔
      ManifestAccepted backend policy expected snapshot profile signature m := by
  unfold checkManifest ManifestAccepted
  split_ifs with h
  · cases policy.lookupKey m.signerId m.keyId <;> simp [h]
  · simp [h]

structure VerificationReport where
  manifest : ProvenanceManifestV1
  authorization : AuthorizationStatus
  deriving DecidableEq

def acceptedReport (m : ProvenanceManifestV1) : VerificationReport := ⟨m, .blocked⟩

/-- Strictly decode the received frame, then check its exact signing message and artifacts. -/
def verifyProvenance (limits : ManifestLimits) (backend : CryptoBackend)
    (policy : VerificationPolicy) (expected : ExpectedContext)
    (frame signature snapshot profile : ByteArray) : Option VerificationReport := do
  let m ← strictDecodeManifest limits frame
  if checkManifest backend policy expected snapshot profile signature m then
    some (acceptedReport m)
  else none

theorem acceptedReport_injective : Function.Injective acceptedReport := by
  intro a b h
  exact congrArg VerificationReport.manifest h

theorem verifyProvenance_eq_some_iff (limits backend policy expected frame signature snapshot
    profile m) :
    verifyProvenance limits backend policy expected frame signature snapshot profile =
      some (acceptedReport m) ↔
    strictDecodeManifest limits frame = some m ∧
      ManifestAccepted backend policy expected snapshot profile signature m := by
  unfold verifyProvenance
  cases hd : strictDecodeManifest limits frame with
  | none => simp
  | some parsed =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split_ifs with h
    · simp only [Option.some.injEq, acceptedReport_injective.eq_iff]
      constructor
      · intro he
        exact ⟨he, he ▸ (checkManifest_iff _ _ _ _ _ _ _).mp h⟩
      · exact fun hh => hh.1
    · simp only [Option.some.injEq, false_iff, not_and]
      intro he ha
      subst parsed
      exact h ((checkManifest_iff _ _ _ _ _ _ _).mpr ha)

/-- Full criterion: canonical framing, size limits, policy and crypto callback acceptance. -/
theorem verifyProvenance_iff (limits backend policy expected frame signature snapshot profile m) :
    verifyProvenance limits backend policy expected frame signature snapshot profile =
      some (acceptedReport m) ↔
    FitsManifestLimits limits m ∧ encodeManifestV1 m = frame ∧
      ManifestAccepted backend policy expected snapshot profile signature m := by
  rw [verifyProvenance_eq_some_iff, decodeManifest_iff]
  exact and_assoc

theorem verify_encoded_iff (limits backend policy expected signature snapshot profile m)
    (hf : FitsManifestLimits limits m) :
    verifyProvenance limits backend policy expected (encodeManifestV1 m) signature snapshot
      profile = some (acceptedReport m) ↔
    ManifestAccepted backend policy expected snapshot profile signature m := by
  rw [verifyProvenance_eq_some_iff, decode_encodeManifestV1 limits m hf]
  simp

theorem report_authorization_blocked (r : VerificationReport) :
    r.authorization = .blocked := by
  cases r.authorization
  rfl

/-- Matching digests are deliberately not promoted to equality of artifact bytes. -/
theorem accepted_artifact_bindings (backend policy expected snapshot profile signature m)
    (h : ManifestAccepted backend policy expected snapshot profile signature m) :
    BindingMatches backend snapshot m.snapshot ∧ BindingMatches backend profile m.profile := by
  obtain ⟨_, key, _, hk⟩ := h
  exact ⟨hk.2.2.2.2.1, hk.2.2.2.2.2.1⟩

theorem accepted_signature (backend policy expected snapshot profile signature m)
    (h : ManifestAccepted backend policy expected snapshot profile signature m) :
    ∃ key, policy.lookupKey m.signerId m.keyId = some key ∧
      backend.verifyEd25519 key (signingMessageV1 m) signature = true := by
  obtain ⟨_, key, hl, hk⟩ := h
  exact ⟨key, hl, hk.2.2.2.2.2.2⟩

theorem unknown_key_rejected (limits backend policy expected frame signature snapshot profile m)
    (hd : strictDecodeManifest limits frame = some m)
    (hk : policy.lookupKey m.signerId m.keyId = none) :
    verifyProvenance limits backend policy expected frame signature snapshot profile = none := by
  simp [verifyProvenance, hd, checkManifest, hk]

theorem revoked_key_rejected (limits backend policy expected frame signature snapshot profile m)
    (hd : strictDecodeManifest limits frame = some m)
    (hr : policy.revoked m.signerId m.keyId = true) :
    verifyProvenance limits backend policy expected frame signature snapshot profile = none := by
  have hc : checkManifest backend policy expected snapshot profile signature m = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨_, key, _, hk⟩ := (checkManifest_iff _ _ _ _ _ _ _).mp h
    simp [KeyChecks, hr] at hk
  simp [verifyProvenance, hd, hc]

theorem changed_challenge_rejected (limits backend policy expected frame signature snapshot
    profile m) (hd : strictDecodeManifest limits frame = some m)
    (hc : m.challenge ≠ expected.challenge) :
    verifyProvenance limits backend policy expected frame signature snapshot profile = none := by
  have hn : manifestContext m ≠ expected := by
    intro he
    exact hc (congrArg ExpectedContext.challenge he)
  simp [verifyProvenance, hd, checkManifest, hn]

structure ProvenanceVerificationSuite : Prop where
  exact_acceptance : ∀ limits backend policy expected frame signature snapshot profile m,
    verifyProvenance limits backend policy expected frame signature snapshot profile =
      some (acceptedReport m) ↔
    FitsManifestLimits limits m ∧ encodeManifestV1 m = frame ∧
      ManifestAccepted backend policy expected snapshot profile signature m
  blocked : ∀ r : VerificationReport, r.authorization = .blocked
  artifact_bindings : ∀ backend policy expected snapshot profile signature m,
    ManifestAccepted backend policy expected snapshot profile signature m →
    BindingMatches backend snapshot m.snapshot ∧ BindingMatches backend profile m.profile
  signature_message : ∀ backend policy expected snapshot profile signature m,
    ManifestAccepted backend policy expected snapshot profile signature m →
    ∃ key, policy.lookupKey m.signerId m.keyId = some key ∧
      backend.verifyEd25519 key (signingMessageV1 m) signature = true

theorem verification_suite : ProvenanceVerificationSuite where
  exact_acceptance := verifyProvenance_iff
  blocked := report_authorization_blocked
  artifact_bindings := accepted_artifact_bindings
  signature_message := accepted_signature
end DigitalProvenanceVerificationContract

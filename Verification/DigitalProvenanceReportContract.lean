/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DigitalProvenanceManifestContract

/-! Bounded, granular provenance composition relative to fallible crypto callbacks.
The explicit request plan models which callbacks the interpreter may invoke;
it is not a theorem about foreign code, compiler evaluation or physical resources.
The older epsilon252/255 acceptance and replay APIs are unchanged. -/
namespace DigitalProvenanceReportContract
open DigitalProvenanceManifestContract

inductive CryptoError where
  | backend_failure
  deriving DecidableEq

structure CryptoBackend where
  sha256 : ByteArray → Except CryptoError Digest256
  verifyEd25519 : ByteArray → ByteArray → ByteArray → Except CryptoError Bool

structure PublicKeyEntry where
  signerId : String
  keyId : String
  roleId : String
  policyVersion : String
  pubKeyBytes : ByteArray
  deriving DecidableEq

structure TrustedTimeWindow where
  scaleId : String
  unitId : String
  minTime : Int
  maxTime : Int
  deriving DecidableEq

structure ExpectedContext where
  contextId : String
  expectedSignerId : String
  expectedRoleId : String
  expectedSessionId : String
  expectedPolicyVersion : String
  expectedN : Nat
  expectedJ : Nat
  expectedEpsilon : ℚ
  keyRegistry : List PublicKeyEntry
  revokedKeys : List (String × String)
  activeChallenge : Option ByteArray
  trustedTimeWindow : Option TrustedTimeWindow

structure VerificationLimits where
  manifest : ManifestLimits
  maxSnapshotSizeBytes : Nat
  maxProfileSizeBytes : Nat
  maxKeyRegistrySize : Nat
  maxRevokedKeys : Nat
  maxContextFieldBytes : Nat

inductive VerificationInputError where
  | limit_exceeded
  deriving DecidableEq

inductive SignatureStatus where
  | valid | invalid_signature | malformed_signature | crypto_backend_failure | not_checked
  deriving DecidableEq
inductive KeyStatus where
  | authorized | unauthorized_key | role_mismatch | policy_mismatch | revoked_key
  | ambiguous_key_registry | not_checked
  deriving DecidableEq
inductive ContextBindingStatus where
  | matched | session_mismatch | context_id_mismatch | parameter_mismatch | not_checked
  deriving DecidableEq
inductive ReplayStatus where
  | challenge_matched | challenge_mismatch | not_checked
  deriving DecidableEq
inductive FreshnessStatus where
  | within_trusted_window | expired | future_timestamp | invalid_time_window
  | time_window_mismatch | untrusted_timestamp | no_timestamp | not_checked
  deriving DecidableEq
inductive ArtifactBindingStatus where
  | matched | digest_mismatch | size_mismatch | crypto_backend_failure | not_checked
  deriving DecidableEq

structure VerificationReport where
  signature : SignatureStatus
  keyAuthorization : KeyStatus
  contextBinding : ContextBindingStatus
  replay : ReplayStatus
  freshness : FreshnessStatus
  snapshotBinding : ArtifactBindingStatus
  profileBinding : ArtifactBindingStatus
  authorization : AuthorizationStatus := .blocked
  deriving DecidableEq

/-- All externally supplied fields have explicit representation bounds. These
checks do not bound pre-existing allocations, encoding work, or wall-clock time. -/
def contextFields (c : ExpectedContext) : List ByteArray :=
  [c.contextId.toUTF8, c.expectedSignerId.toUTF8, c.expectedRoleId.toUTF8,
    c.expectedSessionId.toUTF8, c.expectedPolicyVersion.toUTF8,
    ⟨(CryptoHiddenScalarQuotaCodecContract.encodeNat c.expectedN).toArray⟩,
    ⟨(CryptoHiddenScalarQuotaCodecContract.encodeNat c.expectedJ).toArray⟩,
    ⟨(CryptoHiddenScalarQuotaCodecContract.encodeRat c.expectedEpsilon).toArray⟩] ++
  c.keyRegistry.flatMap (fun k => [k.signerId.toUTF8, k.keyId.toUTF8,
    k.roleId.toUTF8, k.policyVersion.toUTF8, k.pubKeyBytes]) ++
  c.revokedKeys.flatMap (fun k => [k.1.toUTF8, k.2.toUTF8]) ++
  c.activeChallenge.toList ++
  c.trustedTimeWindow.toList.flatMap (fun w => [w.scaleId.toUTF8, w.unitId.toUTF8,
    ⟨(encodeInt w.minTime).toArray⟩, ⟨(encodeInt w.maxTime).toArray⟩])

def InputsFit (l : VerificationLimits) (c : ExpectedContext) (s : SignedProvenanceV1)
    (snapshot profile : ByteArray) : Prop :=
  snapshot.size ≤ l.maxSnapshotSizeBytes ∧ profile.size ≤ l.maxProfileSizeBytes ∧
  c.keyRegistry.length ≤ l.maxKeyRegistrySize ∧ c.revokedKeys.length ≤ l.maxRevokedKeys ∧
  (contextFields c).all (fun b => decide (b.size ≤ l.maxContextFieldBytes)) = true ∧
  FitsManifestLimits l.manifest s.manifest

instance (l c s x y) : Decidable (InputsFit l c s x y) := by
  unfold InputsFit; infer_instance

/-- Key IDs are unique within a signer. Distinct IDs permit rotation. -/
def registryUnique (ks : List PublicKeyEntry) : Bool :=
  decide ((ks.map (fun k => (k.signerId, k.keyId))).Nodup)

def keyCandidates (c : ExpectedContext) (m : ProvenanceManifestV1) : List PublicKeyEntry :=
  c.keyRegistry.filter (fun k => decide (k.signerId = c.expectedSignerId ∧ k.keyId = m.keyId))

/-- A bad registry is rejected globally; no first-match or invalid-entry bypass. -/
def selectKey (c : ExpectedContext) (m : ProvenanceManifestV1) : Except KeyStatus PublicKeyEntry :=
  if registryUnique c.keyRegistry = false then .error .ambiguous_key_registry
  else if c.keyRegistry.any (fun k => decide (k.pubKeyBytes.size ≠ 32)) then
    .error .unauthorized_key
  else if m.signerId ≠ c.expectedSignerId then .error .unauthorized_key
  else if m.roleId ≠ c.expectedRoleId then .error .role_mismatch
  else if m.policyVersion ≠ c.expectedPolicyVersion then .error .policy_mismatch
  else match keyCandidates c m with
  | [k] =>
    if k.roleId ≠ c.expectedRoleId then .error .role_mismatch
    else if k.policyVersion ≠ c.expectedPolicyVersion then .error .policy_mismatch
    else if (c.expectedSignerId, m.keyId) ∈ c.revokedKeys then .error .revoked_key
    else .ok k
  | _ => .error .unauthorized_key

def contextStatus (c : ExpectedContext) (m : ProvenanceManifestV1) : ContextBindingStatus :=
  if m.sessionId ≠ c.expectedSessionId then .session_mismatch
  else if m.expectedContextId ≠ c.contextId then .context_id_mismatch
  else if m.n ≠ c.expectedN ∨ m.j ≠ c.expectedJ ∨ m.epsilon ≠ c.expectedEpsilon then
    .parameter_mismatch
  else .matched

def replayStatus (c : ExpectedContext) (m : ProvenanceManifestV1) : ReplayStatus :=
  match c.activeChallenge with
  | none => .not_checked
  | some b => if m.challenge = b then .challenge_matched else .challenge_mismatch

/-- Validation precedence: malformed external window, missing claim, missing
window, incompatible units, age, future. This checks a claim, not delivery time. -/
def timeStatus (window : Option TrustedTimeWindow) (claim : Option TimeClaim) : FreshnessStatus :=
  match window with
  | none => if claim.isSome then .untrusted_timestamp else .no_timestamp
  | some w =>
    if w.maxTime < w.minTime then .invalid_time_window
    else match claim with
    | none => .no_timestamp
    | some t =>
      if t.scaleId ≠ w.scaleId ∨ t.unitId ≠ w.unitId then .time_window_mismatch
      else if t.value < w.minTime then .expired
      else if w.maxTime < t.value then .future_timestamp
      else .within_trusted_window

structure SignatureRequest where
  key : ByteArray
  message : ByteArray
  signature : ByteArray
  deriving DecidableEq

inductive CryptoRequest where
  | verify : SignatureRequest → CryptoRequest
  | hash : ByteArray → CryptoRequest
  deriving DecidableEq

/-- An absent request retains its precomputed refusal status. -/
structure VerificationPlan where
  initial : VerificationReport
  signatureRequest : Option SignatureRequest
  snapshotRequest : Option ByteArray
  profileRequest : Option ByteArray
  snapshotDigest : Digest256
  profileDigest : Digest256

/-- This function has no backend argument. Requests are data, not callbacks. -/
def planVerification (c : ExpectedContext) (s : SignedProvenanceV1)
    (snapshot profile : ByteArray) : VerificationPlan :=
  let selected := selectKey c s.manifest
  let request := match selected with
    | .error _ => none
    | .ok k => if s.signature.size = 64 then
        some (SignatureRequest.mk k.pubKeyBytes (signingMessageV1 s.manifest) s.signature)
      else none
  { initial := {
      signature := match selected with
        | .error _ => .not_checked
        | .ok _ => if s.signature.size = 64 then .not_checked else .malformed_signature
      keyAuthorization := match selected with | .error e => e | .ok _ => .authorized
      contextBinding := contextStatus c s.manifest
      replay := replayStatus c s.manifest
      freshness := timeStatus c.trustedTimeWindow s.manifest.claimedTime
      snapshotBinding := if snapshot.size = s.manifest.snapshot.sizeBytes then
        .not_checked else .size_mismatch
      profileBinding := if profile.size = s.manifest.profile.sizeBytes then
        .not_checked else .size_mismatch }
    signatureRequest := request
    snapshotRequest := if snapshot.size = s.manifest.snapshot.sizeBytes then some snapshot else none
    profileRequest := if profile.size = s.manifest.profile.sizeBytes then some profile else none
    snapshotDigest := s.manifest.snapshot.digest
    profileDigest := s.manifest.profile.digest }

def prepareVerification (l : VerificationLimits) (c : ExpectedContext) (s : SignedProvenanceV1)
    (snapshot profile : ByteArray) : Except VerificationInputError VerificationPlan :=
  if InputsFit l c s snapshot profile then .ok (planVerification c s snapshot profile)
  else .error .limit_exceeded

def VerificationPlan.requests (p : VerificationPlan) : List CryptoRequest :=
  p.signatureRequest.toList.map .verify ++ p.snapshotRequest.toList.map .hash ++
    p.profileRequest.toList.map .hash

def plannedRequests (l : VerificationLimits) (c : ExpectedContext) (s : SignedProvenanceV1)
    (snapshot profile : ByteArray) : List CryptoRequest :=
  match prepareVerification l c s snapshot profile with
  | .error _ => []
  | .ok p => p.requests

def signatureResult (crypto : CryptoBackend) (old : SignatureStatus)
    (request : Option SignatureRequest) : SignatureStatus :=
  match request with
  | none => old
  | some r => match crypto.verifyEd25519 r.key r.message r.signature with
    | .error _ => .crypto_backend_failure
    | .ok true => .valid
    | .ok false => .invalid_signature

def bindingResult (crypto : CryptoBackend) (old : ArtifactBindingStatus)
    (request : Option ByteArray) (digest : Digest256) : ArtifactBindingStatus :=
  match request with
  | none => old
  | some b => match crypto.sha256 b with
    | .error _ => .crypto_backend_failure
    | .ok d => if d = digest then .matched else .digest_mismatch

/-- The interpreter's only backend applications are the three optional requests,
in signature/snapshot/profile order in the executable definition. -/
def executePlan (crypto : CryptoBackend) (p : VerificationPlan) : VerificationReport :=
  let sig := signatureResult crypto p.initial.signature p.signatureRequest
  let snap := bindingResult crypto p.initial.snapshotBinding p.snapshotRequest p.snapshotDigest
  let prof := bindingResult crypto p.initial.profileBinding p.profileRequest p.profileDigest
  { p.initial with signature := sig, snapshotBinding := snap, profileBinding := prof }

def verifyProvenance (crypto : CryptoBackend) (l : VerificationLimits) (c : ExpectedContext)
    (s : SignedProvenanceV1) (snapshot profile : ByteArray) :
    Except VerificationInputError VerificationReport :=
  match prepareVerification l c s snapshot profile with
  | .error e => .error e
  | .ok p => .ok (executePlan crypto p)

theorem authorization_blocked (r : VerificationReport) : r.authorization = .blocked := by
  cases r.authorization
  rfl

theorem limit_refusal (crypto l c s snapshot profile)
    (h : ¬ InputsFit l c s snapshot profile) :
    verifyProvenance crypto l c s snapshot profile = .error .limit_exceeded ∧
    plannedRequests l c s snapshot profile = [] := by
  simp [verifyProvenance, plannedRequests, prepareVerification, h]

/-- Extensional backend independence is separate from the empty-request theorem. -/
theorem limit_backend_independent (a b l c s x y) (h : ¬ InputsFit l c s x y) :
    verifyProvenance a l c s x y = verifyProvenance b l c s x y := by
  rw [(limit_refusal a l c s x y h).1, (limit_refusal b l c s x y h).1]

theorem selected_key_sound (c m k) (h : selectKey c m = .ok k) :
    k ∈ c.keyRegistry ∧ k.signerId = c.expectedSignerId ∧ k.keyId = m.keyId ∧
    m.signerId = c.expectedSignerId ∧ m.roleId = c.expectedRoleId ∧
    k.roleId = c.expectedRoleId ∧ m.policyVersion = c.expectedPolicyVersion ∧
    k.policyVersion = c.expectedPolicyVersion ∧
    (c.expectedSignerId, m.keyId) ∉ c.revokedKeys ∧ k.pubKeyBytes.size = 32 := by
  unfold selectKey at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hb
  split at h <;> try contradiction
  rename_i hs
  split at h <;> try contradiction
  rename_i hr
  split at h <;> try contradiction
  rename_i hp
  split at h <;> try contradiction
  rename_i entry he
  split at h <;> try contradiction
  rename_i hkr
  split at h <;> try contradiction
  rename_i hkp
  split at h <;> try contradiction
  rename_i hrev
  cases h
  have hm : k ∈ keyCandidates c m := by rw [he]; simp
  obtain ⟨hm, hids⟩ := List.mem_filter.mp hm
  have hi := of_decide_eq_true hids
  have hall : ∀ k ∈ c.keyRegistry, k.pubKeyBytes.size = 32 := by
    simpa only [Bool.not_eq_true, List.any_eq_false, decide_eq_false_iff_not,
      not_not] using hb
  exact ⟨hm, hi.1, hi.2, not_ne_iff.mp hs, not_ne_iff.mp hr,
    not_ne_iff.mp hkr, not_ne_iff.mp hp, not_ne_iff.mp hkp, hrev, hall _ hm⟩

theorem planned_signature_sound (c s x y r)
    (h : (planVerification c s x y).signatureRequest = some r) :
    ∃ k, selectKey c s.manifest = .ok k ∧ r.key = k.pubKeyBytes ∧
      r.message = signingMessageV1 s.manifest ∧ r.signature = s.signature ∧
      s.signature.size = 64 := by
  simp only [planVerification] at h
  cases hk : selectKey c s.manifest with
  | error e => simp [hk] at h
  | ok k =>
    simp only [hk] at h
    split_ifs at h with hn
    · cases h; exact ⟨k, rfl, rfl, rfl, rfl, hn⟩

theorem context_matched_iff (c m) : contextStatus c m = .matched ↔
    m.sessionId = c.expectedSessionId ∧ m.expectedContextId = c.contextId ∧
    m.n = c.expectedN ∧ m.j = c.expectedJ ∧ m.epsilon = c.expectedEpsilon := by
  unfold contextStatus
  split_ifs <;> simp_all
  tauto

theorem challenge_matched_iff (c m) : replayStatus c m = .challenge_matched ↔
    c.activeChallenge = some m.challenge := by
  unfold replayStatus
  cases c.activeChallenge <;> simp [eq_comm]

theorem time_within_iff (window claim) : timeStatus window claim = .within_trusted_window ↔
    ∃ w t, window = some w ∧ claim = some t ∧ w.minTime ≤ w.maxTime ∧
      t.scaleId = w.scaleId ∧ t.unitId = w.unitId ∧
      w.minTime ≤ t.value ∧ t.value ≤ w.maxTime := by
  cases window with
  | none => cases claim <;> simp [timeStatus]
  | some w =>
    cases claim with
    | none => simp [timeStatus]; split_ifs <;> simp
    | some t =>
      simp only [timeStatus]
      split_ifs <;> aesop

/-- A valid signature status entails an actual successful callback on a request. -/
theorem signature_valid_iff (crypto old request) (h : old ≠ SignatureStatus.valid) :
    signatureResult crypto old request = .valid ↔
    ∃ r, request = some r ∧ crypto.verifyEd25519 r.key r.message r.signature = .ok true := by
  cases request with
  | none => simp [signatureResult, h]
  | some r =>
    simp only [signatureResult, Option.some.injEq]
    cases he : crypto.verifyEd25519 r.key r.message r.signature with
    | error e => simp [he]
    | ok b => cases b <;> simp [he]

theorem binding_matched_iff (crypto old request digest) (h : old ≠ ArtifactBindingStatus.matched) :
    bindingResult crypto old request digest = .matched ↔
    ∃ b, request = some b ∧ crypto.sha256 b = .ok digest := by
  cases request with
  | none => simp [bindingResult, h]
  | some b =>
    simp only [bindingResult, Option.some.injEq]
    cases he : crypto.sha256 b with
    | error e => simp [he]
    | ok d => simp [he]

/-- Exact result criterion, without treating a returned report as acceptance. -/
theorem verify_result_iff (crypto l c s x y r) :
    verifyProvenance crypto l c s x y = .ok r ↔
    InputsFit l c s x y ∧ executePlan crypto (planVerification c s x y) = r := by
  unfold verifyProvenance prepareVerification
  split_ifs <;> simp_all

theorem planned_key_authorized_iff (c s x y) :
    (planVerification c s x y).initial.keyAuthorization = .authorized ↔
    ∃ k, selectKey c s.manifest = .ok k := by
  simp only [planVerification]
  cases hk : selectKey c s.manifest with
  | ok k => simp
  | error e =>
    -- selectKey never returns authorized as an error.
    have hn : e ≠ KeyStatus.authorized := by
      unfold selectKey at hk
      repeat' first | (split at hk) | contradiction
      all_goals cases hk; decide
    simp [hn]

theorem planned_initial_signature_not_valid (c s x y) :
    (planVerification c s x y).initial.signature ≠ .valid := by
  simp only [planVerification]
  cases selectKey c s.manifest <;> simp
  split_ifs <;> simp

theorem executed_signature_sound (crypto c s x y)
    (h : (executePlan crypto (planVerification c s x y)).signature = .valid) :
    ∃ k, selectKey c s.manifest = .ok k ∧ s.signature.size = 64 ∧
      crypto.verifyEd25519 k.pubKeyBytes (signingMessageV1 s.manifest) s.signature = .ok true := by
  obtain ⟨r, hr, hv⟩ := (signature_valid_iff crypto _ _
    (planned_initial_signature_not_valid c s x y)).mp h
  obtain ⟨k, hk, hkey, hmsg, hsig, hsize⟩ := planned_signature_sound c s x y r hr
  exact ⟨k, hk, hsize, by simpa only [hkey, hmsg, hsig] using hv⟩

theorem executed_snapshot_matched_iff (crypto c s x y) :
    (executePlan crypto (planVerification c s x y)).snapshotBinding = .matched ↔
    x.size = s.manifest.snapshot.sizeBytes ∧ crypto.sha256 x = .ok s.manifest.snapshot.digest := by
  simp only [executePlan, planVerification]
  split_ifs with h
  · rw [binding_matched_iff crypto _ _ _ (by decide)]
    simp [h]
  · simp [bindingResult, h]

theorem executed_profile_matched_iff (crypto c s x y) :
    (executePlan crypto (planVerification c s x y)).profileBinding = .matched ↔
    y.size = s.manifest.profile.sizeBytes ∧ crypto.sha256 y = .ok s.manifest.profile.digest := by
  simp only [executePlan, planVerification]
  split_ifs with h
  · rw [binding_matched_iff crypto _ _ _ (by decide)]
    simp [h]
  · simp [bindingResult, h]

theorem executed_context_iff (crypto c s x y) :
    (executePlan crypto (planVerification c s x y)).contextBinding = .matched ↔
    s.manifest.sessionId = c.expectedSessionId ∧ s.manifest.expectedContextId = c.contextId ∧
    s.manifest.n = c.expectedN ∧ s.manifest.j = c.expectedJ ∧
    s.manifest.epsilon = c.expectedEpsilon := context_matched_iff c s.manifest

theorem executed_challenge_iff (crypto c s x y) :
    (executePlan crypto (planVerification c s x y)).replay = .challenge_matched ↔
    c.activeChallenge = some s.manifest.challenge := challenge_matched_iff c s.manifest

theorem executed_time_iff (crypto c s x y) :
    (executePlan crypto (planVerification c s x y)).freshness = .within_trusted_window ↔
    ∃ w t, c.trustedTimeWindow = some w ∧ s.manifest.claimedTime = some t ∧
      w.minTime ≤ w.maxTime ∧ t.scaleId = w.scaleId ∧ t.unitId = w.unitId ∧
      w.minTime ≤ t.value ∧ t.value ≤ w.maxTime :=
  time_within_iff c.trustedTimeWindow s.manifest.claimedTime

theorem key_refusal_no_signature (c s x y e) (h : selectKey c s.manifest = .error e) :
    (planVerification c s x y).signatureRequest = none := by
  simp [planVerification, h]

theorem malformed_signature_no_request (c s x y) (h : s.signature.size ≠ 64) :
    (planVerification c s x y).signatureRequest = none := by
  simp only [planVerification]
  cases selectKey c s.manifest <;> simp [h]

/-- End-to-end success is tied to an external registered key and exact bytes.
No assumption about the cryptographic correctness of the callback is introduced. -/
theorem verified_signature_external (crypto l c s x y r)
    (hr : verifyProvenance crypto l c s x y = .ok r) (hs : r.signature = .valid) :
    ∃ k, k ∈ c.keyRegistry ∧ k.signerId = c.expectedSignerId ∧
      k.keyId = s.manifest.keyId ∧ k.roleId = c.expectedRoleId ∧
      k.policyVersion = c.expectedPolicyVersion ∧ k.pubKeyBytes.size = 32 ∧
      s.signature.size = 64 ∧
      crypto.verifyEd25519 k.pubKeyBytes (signingMessageV1 s.manifest) s.signature = .ok true := by
  obtain ⟨_, he⟩ := (verify_result_iff crypto l c s x y r).mp hr
  rw [← he] at hs
  obtain ⟨k, hk, hsize, hv⟩ := executed_signature_sound crypto c s x y hs
  obtain ⟨hm, hi, hid, _, _, hrole, _, hp, _, hlen⟩ := selected_key_sound c s.manifest k hk
  exact ⟨k, hm, hi, hid, hrole, hp, hlen, hsize, hv⟩

structure ProvenanceReportSuite : Prop where
  blocked : ∀ r : VerificationReport, r.authorization = .blocked
  preflight_refusal : ∀ crypto l c s x y, ¬ InputsFit l c s x y →
    verifyProvenance crypto l c s x y = .error .limit_exceeded ∧ plannedRequests l c s x y = []
  exact_result : ∀ crypto l c s x y r, verifyProvenance crypto l c s x y = .ok r ↔
    InputsFit l c s x y ∧ executePlan crypto (planVerification c s x y) = r
  signature_sound : ∀ crypto c s x y,
    (executePlan crypto (planVerification c s x y)).signature = .valid →
    ∃ k, selectKey c s.manifest = .ok k ∧ s.signature.size = 64 ∧
      crypto.verifyEd25519 k.pubKeyBytes (signingMessageV1 s.manifest) s.signature = .ok true

theorem verification_suite : ProvenanceReportSuite where
  blocked := authorization_blocked
  preflight_refusal := limit_refusal
  exact_result := verify_result_iff
  signature_sound := executed_signature_sound

end DigitalProvenanceReportContract

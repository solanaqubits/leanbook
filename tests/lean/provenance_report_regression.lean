import Verification.DigitalProvenanceReportContract
open DigitalProvenanceManifestContract DigitalProvenanceReportContract

-- Synthetic callbacks only; no SHA-256 or Ed25519 conformance is asserted.
private def digest (x : UInt8) : Digest256 :=
  ⟨⟨Array.replicate 32 x⟩, by simp [ByteArray.size]⟩
private def snap : ByteArray := ⟨#[1, 2, 3]⟩
private def prof : ByteArray := ⟨#[4, 5]⟩
private def key : ByteArray := ⟨Array.replicate 32 7⟩
private def sig : ByteArray := ⟨Array.replicate 64 9⟩
private def timeClaim : TimeClaim := ⟨"scale", "ticks", -3⟩
private def m : ProvenanceManifestV1 :=
  ⟨"signer", "key", "role", "session", ⟨#[10, 20]⟩, "policy",
    ⟨3, digest 1⟩, ⟨2, digest 2⟩, 3, 1, -1/2, "context", some timeClaim⟩
private def entry : PublicKeyEntry := ⟨"signer", "key", "role", "policy", key⟩
private def window : TrustedTimeWindow := ⟨"scale", "ticks", -5, 0⟩
private def ctx : ExpectedContext :=
  ⟨"context", "signer", "role", "session", "policy", 3, 1, -1/2,
    [entry], [], some m.challenge, some window⟩
private def limits : VerificationLimits := ⟨⟨4096, 128, 32⟩, 1024, 1024, 16, 16, 128⟩
private def backend : CryptoBackend :=
  ⟨fun b => .ok (if b = snap then digest 1 else if b = prof then digest 2 else digest 3),
   fun _ _ _ => .ok true⟩
private def good : VerificationReport :=
  ⟨.valid, .authorized, .matched, .challenge_matched, .within_trusted_window,
    .matched, .matched, .blocked⟩
private def run (c := ctx) (mm := m) (signature := sig) (snapshot := snap) (profile := prof)
    (b := backend) (l := limits) : Except VerificationInputError VerificationReport :=
  verifyProvenance b l c ⟨mm, signature⟩ snapshot profile
private def withTime (t : Int) : ProvenanceManifestV1 :=
  { m with claimedTime := some { timeClaim with value := t } }
private def keyFailure (status : KeyStatus) : VerificationReport :=
  { good with signature := .not_checked, keyAuthorization := status }

example (a b l c s x y) (h : ¬ InputsFit l c s x y) :
    verifyProvenance a l c s x y = verifyProvenance b l c s x y :=
  limit_backend_independent a b l c s x y h
example (c m k) (h : selectKey c m = .ok k) : k ∈ c.keyRegistry :=
  (selected_key_sound c m k h).1
example (c s x y r) (h : (planVerification c s x y).signatureRequest = some r) :
    r.message = signingMessageV1 s.manifest := by
  obtain ⟨_, _, _, hm, _⟩ := planned_signature_sound c s x y r h
  exact hm
example (crypto c s x y) :
    (executePlan crypto (planVerification c s x y)).snapshotBinding = .matched ↔
    x.size = s.manifest.snapshot.sizeBytes ∧ crypto.sha256 x = .ok s.manifest.snapshot.digest :=
  executed_snapshot_matched_iff crypto c s x y

def main : IO Unit := do
  let cases : List (String × Bool) := [
    ("positive", decide (run = .ok good)),
    ("unknown key", decide (run (c := { ctx with keyRegistry := [] }) = .ok (keyFailure .unauthorized_key))),
    ("duplicate key", decide (run (c := { ctx with keyRegistry := [entry, entry] }) = .ok (keyFailure .ambiguous_key_registry))),
    ("conflicting role", decide (run (c := { ctx with keyRegistry := [entry, {entry with roleId := "other"}] }) = .ok (keyFailure .ambiguous_key_registry))),
    ("conflicting public bytes", decide (run (c := { ctx with keyRegistry := [entry, {entry with pubKeyBytes := ⟨Array.replicate 32 8⟩}] }) = .ok (keyFailure .ambiguous_key_registry))),
    ("rotation allowed", decide (run (c := { ctx with keyRegistry := [entry, {entry with keyId := "next"}] }) = .ok good)),
    ("rotation new key id", decide (run (c := { ctx with keyRegistry := [entry, {entry with keyId := "next"}] }) (mm := {m with keyId := "next"}) = .ok good)),
    ("unregistered key id", decide (run (mm := {m with keyId := "next"}) = .ok (keyFailure .unauthorized_key))),
    ("different signer same key id", decide (run (c := {ctx with keyRegistry := [entry, {entry with signerId := "other"}]}) = .ok good)),
    ("malformed key", decide (run (c := { ctx with keyRegistry := [{entry with pubKeyBytes := ⟨#[]⟩}] }) = .ok (keyFailure .unauthorized_key))),
    ("unrelated malformed key rejected", decide (run (c := { ctx with keyRegistry := [entry, {entry with keyId := "other", pubKeyBytes := ⟨#[]⟩}] }) = .ok (keyFailure .unauthorized_key))),
    ("signer spoof", decide (run (mm := {m with signerId := "other"}) = .ok (keyFailure .unauthorized_key))),
    ("external signer changed", decide (run (c := {ctx with expectedSignerId := "other"}) = .ok (keyFailure .unauthorized_key))),
    ("manifest role", decide (run (mm := {m with roleId := "other"}) = .ok (keyFailure .role_mismatch))),
    ("registry role", decide (run (c := {ctx with keyRegistry := [{entry with roleId := "other"}]}) = .ok (keyFailure .role_mismatch))),
    ("expected role", decide (run (c := {ctx with expectedRoleId := "other"}) = .ok (keyFailure .role_mismatch))),
    ("manifest policy", decide (run (mm := {m with policyVersion := "other"}) = .ok (keyFailure .policy_mismatch))),
    ("registry policy", decide (run (c := {ctx with keyRegistry := [{entry with policyVersion := "other"}]}) = .ok (keyFailure .policy_mismatch))),
    ("expected policy", decide (run (c := {ctx with expectedPolicyVersion := "other"}) = .ok (keyFailure .policy_mismatch))),
    ("revoked", decide (run (c := {ctx with revokedKeys := [("signer", "key")]}) = .ok (keyFailure .revoked_key))),
    ("revocation scoped", decide (run (c := {ctx with revokedKeys := [("other", "key")]}) = .ok good)),
    ("short signature", decide (run (signature := ⟨Array.replicate 63 9⟩) = .ok {good with signature := .malformed_signature})),
    ("long signature", decide (run (signature := ⟨Array.replicate 65 9⟩) = .ok {good with signature := .malformed_signature})),
    ("signature false", decide (run (b := {backend with verifyEd25519 := fun _ _ _ => .ok false}) = .ok {good with signature := .invalid_signature})),
    ("signature backend failure", decide (run (b := {backend with verifyEd25519 := fun _ _ _ => .error .backend_failure}) = .ok {good with signature := .crypto_backend_failure})),
    ("hash backend failure", decide (run (b := {backend with sha256 := fun _ => .error .backend_failure}) = .ok {good with snapshotBinding := .crypto_backend_failure, profileBinding := .crypto_backend_failure})),
    ("exact signature message", decide (run (b := {backend with verifyEd25519 := fun k msg s => .ok (decide (k = key ∧ msg = signingMessageV1 m ∧ s = sig))}) = .ok good)),
    ("no removed domain", decide (run (b := {backend with verifyEd25519 := fun _ msg _ => .ok (decide (msg = encodeManifestV1 m))}) = .ok {good with signature := .invalid_signature})),
    ("session", decide (run (c := {ctx with expectedSessionId := "other"}) = .ok {good with contextBinding := .session_mismatch})),
    ("context id", decide (run (c := {ctx with contextId := "other"}) = .ok {good with contextBinding := .context_id_mismatch})),
    ("n", decide (run (c := {ctx with expectedN := 4}) = .ok {good with contextBinding := .parameter_mismatch})),
    ("j", decide (run (c := {ctx with expectedJ := 2}) = .ok {good with contextBinding := .parameter_mismatch})),
    ("epsilon", decide (run (c := {ctx with expectedEpsilon := 0}) = .ok {good with contextBinding := .parameter_mismatch})),
    ("challenge mismatch", decide (run (c := {ctx with activeChallenge := some ⟨#[]⟩}) = .ok {good with replay := .challenge_mismatch})),
    ("challenge not supplied", decide (run (c := {ctx with activeChallenge := none}) = .ok {good with replay := .not_checked})),
    ("no replay consumption", decide (run = run ∧ run = .ok good)),
    ("lower time boundary", decide (run (mm := withTime (-5)) = .ok good)),
    ("upper time boundary", decide (run (mm := withTime 0) = .ok good)),
    ("expired", decide (run (mm := withTime (-6)) = .ok {good with freshness := .expired})),
    ("future", decide (run (mm := withTime 1) = .ok {good with freshness := .future_timestamp})),
    ("invalid window", decide (run (c := {ctx with trustedTimeWindow := some {window with minTime := 1}}) = .ok {good with freshness := .invalid_time_window})),
    ("scale mismatch", decide (run (c := {ctx with trustedTimeWindow := some {window with scaleId := "other"}}) = .ok {good with freshness := .time_window_mismatch})),
    ("unit mismatch", decide (run (c := {ctx with trustedTimeWindow := some {window with unitId := "other"}}) = .ok {good with freshness := .time_window_mismatch})),
    ("untrusted time", decide (run (c := {ctx with trustedTimeWindow := none}) = .ok {good with freshness := .untrusted_timestamp})),
    ("missing timestamp", decide (run (mm := {m with claimedTime := none}) = .ok {good with freshness := .no_timestamp})),
    ("no time and no window", decide (run (mm := {m with claimedTime := none}) (c := {ctx with trustedTimeWindow := none}) = .ok {good with freshness := .no_timestamp})),
    ("bad window precedes absent timestamp", decide (run (mm := {m with claimedTime := none}) (c := {ctx with trustedTimeWindow := some {window with minTime := 1}}) = .ok {good with freshness := .invalid_time_window})),
    ("snapshot size", decide (run (snapshot := ⟨#[]⟩) = .ok {good with snapshotBinding := .size_mismatch})),
    ("profile size", decide (run (profile := ⟨#[]⟩) = .ok {good with profileBinding := .size_mismatch})),
    ("snapshot digest", decide (run (snapshot := ⟨#[9, 9, 9]⟩) = .ok {good with snapshotBinding := .digest_mismatch})),
    ("profile digest", decide (run (profile := ⟨#[9, 9]⟩) = .ok {good with profileBinding := .digest_mismatch})),
    ("global manifest limit", decide (run (l := {limits with manifest := {limits.manifest with maxManifestSizeBytes := 0}}) = .error .limit_exceeded)),
    ("string limit", decide (run (l := {limits with manifest := {limits.manifest with maxStringBytes := 0}}) = .error .limit_exceeded)),
    ("challenge limit", decide (run (l := {limits with manifest := {limits.manifest with maxChallengeBytes := 0}}) = .error .limit_exceeded)),
    ("snapshot limit", decide (run (l := {limits with maxSnapshotSizeBytes := 2}) = .error .limit_exceeded)),
    ("profile limit", decide (run (l := {limits with maxProfileSizeBytes := 1}) = .error .limit_exceeded)),
    ("registry limit", decide (run (l := {limits with maxKeyRegistrySize := 0}) = .error .limit_exceeded)),
    ("revocation limit", decide (run (c := {ctx with revokedKeys := [("other", "key")]}) (l := {limits with maxRevokedKeys := 0}) = .error .limit_exceeded)),
    ("context fields", decide (run (l := {limits with maxContextFieldBytes := 0}) = .error .limit_exceeded)),
    ("giant expected integer", decide (run (c := {ctx with expectedN := 2^1024}) = .error .limit_exceeded)),
    ("giant expected rational", decide (run (c := {ctx with expectedEpsilon := (2^1024 : ℚ)}) = .error .limit_exceeded)),
    ("giant expected challenge", decide (run (c := {ctx with activeChallenge := some ⟨Array.replicate 129 0⟩}) = .error .limit_exceeded)),
    ("empty plan on limit", decide (plannedRequests {limits with maxKeyRegistrySize := 0} ctx ⟨m, sig⟩ snap prof = [])),
    ("exact request order", decide (plannedRequests limits ctx ⟨m, sig⟩ snap prof = [.verify ⟨key, signingMessageV1 m, sig⟩, .hash snap, .hash prof])),
    ("no signature request without key", decide (plannedRequests limits {ctx with keyRegistry := []} ⟨m, sig⟩ snap prof = [.hash snap, .hash prof])),
    ("no hash on size mismatch", decide (plannedRequests limits ctx ⟨m, sig⟩ ⟨#[]⟩ prof = [.verify ⟨key, signingMessageV1 m, sig⟩, .hash prof])),
    ("malformed signature not requested", decide (plannedRequests limits ctx ⟨m, ⟨#[]⟩⟩ snap prof = [.hash snap, .hash prof])),
    ("size refusal before hash failure", decide (run (snapshot := ⟨#[]⟩) (b := {backend with sha256 := fun _ => .error .backend_failure}) = .ok {good with snapshotBinding := .size_mismatch, profileBinding := .crypto_backend_failure})),
    ("bad signature does not erase bindings", decide (run (b := {backend with verifyEd25519 := fun _ _ _ => .ok false}) = .ok {good with signature := .invalid_signature}))]
  for (label, passed) in cases do
    unless passed do throw (IO.userError label)
  IO.println s!"PROVENANCE_REPORT_OK {cases.length}"

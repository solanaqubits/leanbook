import Verification.DigitalProvenanceVerificationContract
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract

-- Deliberately synthetic callbacks: these are control-flow tests, not crypto vectors.
private def digest (x : UInt8) : Digest256 :=
  ⟨⟨Array.replicate 32 x⟩, by simp [ByteArray.size]⟩
private def snap : ByteArray := ⟨#[1, 2, 3]⟩
private def prof : ByteArray := ⟨#[4, 5]⟩
private def key : ByteArray := ⟨Array.replicate 32 7⟩
private def sig : ByteArray := ⟨Array.replicate 64 9⟩
private def timeClaim : TimeClaim := ⟨"external-scale", "ticks", -3⟩
private def m : ProvenanceManifestV1 :=
  ⟨"signer", "key", "role", "session", ⟨#[10, 20]⟩, "policy-v1",
    ⟨3, digest 1⟩, ⟨2, digest 2⟩, 3, 1, -1/2, "context", some timeClaim⟩
private def expected : ExpectedContext := manifestContext m
private def limits : ManifestLimits := ⟨4096, 128, 32⟩
private def backend : CryptoBackend :=
  ⟨fun b => if b = snap then digest 1 else if b = prof then digest 2 else digest 3,
   fun k msg s => decide (k = key ∧ msg = signingMessageV1 m ∧ s = sig)⟩
private def policy : VerificationPolicy :=
  ⟨fun signer kid => if signer = "signer" ∧ kid = "key" then some key else none,
   fun _ _ => false, fun t => decide (t = some timeClaim)⟩
private def check (b := backend) (p := policy) (e := expected) (mm := m)
    (signature := sig) (snapshot := snap) (profile := prof) : Option VerificationReport :=
  verifyProvenance limits b p e (encodeManifestV1 mm) signature snapshot profile
private def loose : CryptoBackend := { backend with verifyEd25519 := fun _ _ _ => true }
private def accepted := some (acceptedReport m)

example (l b p e f s x y mm) :
    verifyProvenance l b p e f s x y = some (acceptedReport mm) ↔
    FitsManifestLimits l mm ∧ encodeManifestV1 mm = f ∧
      ManifestAccepted b p e x y s mm := verifyProvenance_iff _ _ _ _ _ _ _ _ _
example (r : VerificationReport) : r.authorization = .blocked :=
  report_authorization_blocked r
example (b p e x y s mm) (h : ManifestAccepted b p e x y s mm) :
    BindingMatches b x mm.snapshot ∧ BindingMatches b y mm.profile :=
  accepted_artifact_bindings _ _ _ _ _ _ _ h
example (b p e x y s mm) (h : ManifestAccepted b p e x y s mm) :
    ∃ k, p.lookupKey mm.signerId mm.keyId = some k ∧
      b.verifyEd25519 k (signingMessageV1 mm) s = true :=
  accepted_signature _ _ _ _ _ _ _ h
example (l b p e f s x y mm) (hd : strictDecodeManifest l f = some mm)
    (h : p.lookupKey mm.signerId mm.keyId = none) :
    verifyProvenance l b p e f s x y = none := unknown_key_rejected _ _ _ _ _ _ _ _ _ hd h
example (l b p e f s x y mm) (hd : strictDecodeManifest l f = some mm)
    (h : p.revoked mm.signerId mm.keyId = true) :
    verifyProvenance l b p e f s x y = none := revoked_key_rejected _ _ _ _ _ _ _ _ _ hd h
example (l b p e f s x y mm) (hd : strictDecodeManifest l f = some mm)
    (h : mm.challenge ≠ e.challenge) :
    verifyProvenance l b p e f s x y = none := changed_challenge_rejected _ _ _ _ _ _ _ _ _ hd h

def main : IO Unit := do
  let cases : List (String × Bool) := [
    ("accept", decide (check = accepted)),
    ("unknown key", decide (check (p := { policy with lookupKey := fun _ _ => none }) = none)),
    ("revoked key", decide (check (p := { policy with revoked := fun _ _ => true }) = none)),
    ("time rejected", decide (check (p := { policy with acceptsTime := fun _ => false }) = none)),
    ("signature rejected", decide (check (b := { backend with verifyEd25519 := fun _ _ _ => false }) = none)),
    ("bad signature bytes", decide (check (signature := ⟨Array.replicate 64 8⟩) = none)),
    ("short signature", decide (check (b := loose) (signature := ⟨Array.replicate 63 9⟩) = none)),
    ("long signature", decide (check (b := loose) (signature := ⟨Array.replicate 65 9⟩) = none)),
    ("short public key", decide (check (b := loose) (p := { policy with lookupKey := fun _ _ => some ⟨Array.replicate 31 7⟩ }) = none)),
    ("long public key", decide (check (b := loose) (p := { policy with lookupKey := fun _ _ => some ⟨Array.replicate 33 7⟩ }) = none)),
    ("signer mismatch", decide (check (e := { expected with signerId := "other" }) = none)),
    ("key id mismatch", decide (check (e := { expected with keyId := "other" }) = none)),
    ("role mismatch", decide (check (e := { expected with roleId := "other" }) = none)),
    ("session mismatch", decide (check (e := { expected with sessionId := "other" }) = none)),
    ("challenge mismatch", decide (check (e := { expected with challenge := ⟨#[10, 21]⟩ }) = none)),
    ("policy version mismatch", decide (check (e := { expected with policyVersion := "other" }) = none)),
    ("n mismatch", decide (check (e := { expected with n := 4 }) = none)),
    ("j mismatch", decide (check (e := { expected with j := 2 }) = none)),
    ("epsilon mismatch", decide (check (e := { expected with epsilon := 0 }) = none)),
    ("context id mismatch", decide (check (e := { expected with expectedContextId := "other" }) = none)),
    ("missing time", decide (check (b := loose) (mm := { m with claimedTime := none }) = none)),
    ("time scale mismatch", decide (check (b := loose) (mm := { m with claimedTime := some { timeClaim with scaleId := "other" } }) = none)),
    ("time unit mismatch", decide (check (b := loose) (mm := { m with claimedTime := some { timeClaim with unitId := "other" } }) = none)),
    ("time value mismatch", decide (check (b := loose) (mm := { m with claimedTime := some { timeClaim with value := 10 } }) = none)),
    ("snapshot digest mismatch", decide (check (snapshot := ⟨#[1, 2, 4]⟩) = none)),
    ("profile digest mismatch", decide (check (profile := ⟨#[4, 6]⟩) = none)),
    ("snapshot size mismatch", decide (check (b := { loose with sha256 := fun _ => digest 1 }) (snapshot := ⟨#[1]⟩) = none)),
    ("profile size mismatch", decide (check (b := { loose with sha256 := fun _ => digest 2 }) (profile := ⟨#[1]⟩) = none)),
    ("swapped artifacts", decide (check (snapshot := prof) (profile := snap) = none)),
    ("malformed empty frame", decide (verifyProvenance limits backend policy expected ⟨#[]⟩ sig snap prof = none)),
    ("trailing byte", decide (verifyProvenance limits backend policy expected (encodeManifestV1 m ++ ⟨#[0]⟩) sig snap prof = none)),
    ("manifest limit", decide (verifyProvenance ⟨0, 128, 32⟩ backend policy expected (encodeManifestV1 m) sig snap prof = none)),
    ("string limit", decide (verifyProvenance ⟨4096, 0, 32⟩ backend policy expected (encodeManifestV1 m) sig snap prof = none)),
    ("challenge limit", decide (verifyProvenance ⟨4096, 128, 0⟩ backend policy expected (encodeManifestV1 m) sig snap prof = none)),
    ("no prehash or duplicate domain", decide (check (b := { backend with verifyEd25519 := fun _ msg _ => decide (msg = encodeManifestV1 m) }) = none)),
    ("pure replay is not consumed", decide (check = accepted ∧ check = accepted)),
    ("authorization blocked", decide ((check.map (·.authorization)) = some .blocked))]
  for (label, passed) in cases do
    unless passed do throw (IO.userError label)
  -- A deliberately colliding hash accepts changed equal-size bytes. The contract
  -- guarantees comparison against callbacks, never cryptographic authenticity.
  let colliding : CryptoBackend := ⟨fun _ => digest 1, fun _ _ _ => true⟩
  let cm := { m with profile := ⟨2, digest 1⟩ }
  unless check (b := colliding) (mm := cm) (snapshot := ⟨#[99, 98, 97]⟩) =
      some (acceptedReport cm) do throw (IO.userError "backend trust boundary")
  IO.println s!"PROVENANCE_VERIFIER_OK {cases.length + 1}"

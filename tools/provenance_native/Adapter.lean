import tools.provenance_native.Raw
import Verification.DigitalProvenanceReportContract

/-! Runtime-only effectful adapter. Never imported by Verification or its theorem registry.
The pure epsilon258 backend is not populated with hidden IO. -/
namespace ProvenanceNative
open DigitalProvenanceManifestContract DigitalProvenanceReportContract

structure Config where
  libraryPath : String
  expectedVersion : String


structure IOBackend where
  sha256 : ByteArray → IO (Except CryptoError Digest256)
  verifyEd25519 : ByteArray → ByteArray → ByteArray → IO (Except CryptoError Bool)

def nativeBackend (config : Config) : IOBackend where
  sha256 bytes := do
    try
      let raw ← rawHash config.libraryPath config.expectedVersion bytes
      if h : raw.size = 32 then return .ok ⟨raw, h⟩
      else return .error .backend_failure
    catch _ => return .error .backend_failure
  verifyEd25519 key message signature := do
    if key.size ≠ 32 ∨ signature.size ≠ 64 then return .error .backend_failure
    try
      match ← rawVerify config.libraryPath config.expectedVersion key message signature with
      | 0 => return .ok false
      | 1 => return .ok true
      | _ => return .error .backend_failure
    catch _ => return .error .backend_failure

structure Answers where
  signature : Option (Except CryptoError Bool)
  snapshot : Option (Except CryptoError Digest256)
  profile : Option (Except CryptoError Digest256)

structure Execution where
  report : VerificationReport
  requests : List CryptoRequest
  answers : Answers

/-- Interpret only the preflight-produced requests, in explicit IO sequence.
Exceptions from a supplied IO backend become controlled failures; fatal crashes
and nontermination are outside this contract. -/
def execute (backend : IOBackend) (p : VerificationPlan) : IO Execution := do
  let (signature, sigAnswer) ← match p.signatureRequest with
    | none => pure (p.initial.signature, none)
    | some r => do
      let answer ← try backend.verifyEd25519 r.key r.message r.signature
                    catch _ => pure (.error .backend_failure)
      let status := match answer with
        | .ok true => SignatureStatus.valid
        | .ok false => .invalid_signature
        | .error _ => .crypto_backend_failure
      pure (status, some answer)
  let binding (request : Option ByteArray) (old : ArtifactBindingStatus) (digest : Digest256) := do
    match request with
    | none => pure (old, none)
    | some bytes =>
      let answer ← try backend.sha256 bytes catch _ => pure (.error .backend_failure)
      let status := match answer with
        | .error _ => ArtifactBindingStatus.crypto_backend_failure
        | .ok d => if d = digest then .matched else .digest_mismatch
      pure (status, some answer)
  let (snapshot, snapAnswer) ← binding p.snapshotRequest p.initial.snapshotBinding p.snapshotDigest
  let (profile, profAnswer) ← binding p.profileRequest p.initial.profileBinding p.profileDigest
  let report : VerificationReport := { p.initial with
    signature := signature
    snapshotBinding := snapshot
    profileBinding := profile }
  return ⟨report, p.requests, ⟨sigAnswer, snapAnswer, profAnswer⟩⟩

/-- Typed input; raw manifest decoding and independently sourced context precede this API. -/
def verifyProvenanceIO (backend : IOBackend) (limits : VerificationLimits)
    (ctx : ExpectedContext) (signed : SignedProvenanceV1) (snapshot profile : ByteArray) :
    IO (Except VerificationInputError Execution) := do
  match prepareVerification limits ctx signed snapshot profile with
  | .error e => return .error e
  | .ok p => return .ok (← execute backend p)

/-- Explicit finite response model for conformance comparison, not a native pure backend.
Unrequested inputs fail. If two identical hash requests yielded different responses,
this finite model cannot explain both; comparison must then fail. -/
def responseModel (p : VerificationPlan) (a : Answers) : CryptoBackend where
  sha256 bytes :=
    if p.snapshotRequest = some bytes then a.snapshot.getD (.error .backend_failure)
    else if p.profileRequest = some bytes then a.profile.getD (.error .backend_failure)
    else .error .backend_failure
  verifyEd25519 key message signature :=
    if p.signatureRequest = some ⟨key, message, signature⟩ then
      a.signature.getD (.error .backend_failure)
    else .error .backend_failure

def conforms (p : VerificationPlan) (e : Execution) : Bool :=
  let model := responseModel p e.answers
  let signatureAnswer := p.signatureRequest.map (fun r =>
    model.verifyEd25519 r.key r.message r.signature)
  let snapshotAnswer := p.snapshotRequest.map model.sha256
  let profileAnswer := p.profileRequest.map model.sha256
  decide (executePlan model p = e.report ∧ e.requests = p.requests ∧
    signatureAnswer = e.answers.signature ∧ snapshotAnswer = e.answers.snapshot ∧
    profileAnswer = e.answers.profile)
end ProvenanceNative

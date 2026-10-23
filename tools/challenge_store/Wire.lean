import Lean
import tools.provenance_native.Adapter
import Verification.DigitalProvenanceChallengeRegistryContract

/-! Runtime transport only. These JSON instances are not imported by the formal registry. -/
namespace ChallengeStore
open Lean DigitalProvenanceManifestContract DigitalProvenanceReportContract
open DigitalProvenanceChallengeRegistryContract

instance : ToJson ByteArray := ⟨fun b => toJson (b.data.toList.map UInt8.toNat)⟩
instance : FromJson ByteArray where
  fromJson? j := do
    let ns : List Nat ← fromJson? j
    if ns.any (· > 255) then throw "invalid byte"
    return ⟨(ns.map Nat.toUInt8).toArray⟩
instance : ToJson ℚ := ⟨fun q => toJson (q.num, q.den)⟩
instance : FromJson ℚ where
  fromJson? j := do
    let (a, b) : Int × Nat ← fromJson? j
    if b = 0 || Nat.gcd a.natAbs b != 1 then throw "noncanonical rational"
    return (a : ℚ) / (b : ℚ)
instance : ToJson Digest256 := ⟨fun d => toJson d.bytes⟩
instance : FromJson Digest256 where
  fromJson? j := do
    let b : ByteArray ← fromJson? j
    if h : b.size = 32 then return ⟨b, h⟩ else throw "invalid digest size"

deriving instance ToJson, FromJson for ArtifactBinding, TimeClaim, ProvenanceManifestV1,
  SignedProvenanceV1, AuthorizationStatus, ManifestLimits, PublicKeyEntry, TrustedTimeWindow,
  ExpectedContext, VerificationLimits, SignatureStatus, KeyStatus, ContextBindingStatus,
  ReplayStatus, FreshnessStatus, ArtifactBindingStatus, VerificationReport,
  Scope, ChallengeKey, ContextConfig, Request, Binding, ConsumedRecord,
  EntryState, RedemptionFailure, AcceptanceKind, RedemptionResult, TransactionState,
  ResolutionResult, Input, Output

structure Image where
  entries : List (ChallengeKey × EntryState) := []
  transactions : List (TransactionId × TransactionState) := []
  contexts : List (String × ContextConfig) := []
  active : List (Scope × String) := []
  accepted : List ChallengeKey := []
  deriving ToJson, FromJson

def lookupMap {α β} [DecidableEq α] (xs : List (α × β)) (a : α) : Option β :=
  (xs.find? (fun x => x.1 = a)).map Prod.snd

def Image.state (x : Image) : State :=
  ⟨lookupMap x.entries, lookupMap x.transactions, lookupMap x.contexts,
   lookupMap x.active, x.accepted⟩

def materialize (old : Image) (i : Input) (s : State) : Image := Id.run do
  let mut ks := old.entries.map Prod.fst
  let mut ts := old.transactions.map Prod.fst
  let mut vs := old.contexts.map Prod.fst
  let mut scopes := old.active.map Prod.fst
  match i with
  | .issue k => ks := (k :: ks).dedup
  | .beginTransaction t _ => ts := (t :: ts).dedup
  | .installContext v c =>
    vs := (v :: vs).dedup
    scopes := (scopeOf c.expected :: scopes).dedup
  | _ => pure ()
  return ⟨ks.filterMap (fun k => (s.entries k).map (k, ·)),
    ts.filterMap (fun t => (s.transactions t).map (t, ·)),
    vs.filterMap (fun v => (s.contexts v).map (v, ·)),
    scopes.filterMap (fun k => (s.active k).map (k, ·)), s.accepted⟩

/-- Fetch finite native answers in IO; replay the pure step with this explicit response table.
No effects are disguised as the pure backend. Unrequested queries fail. -/
def collect (backend : ProvenanceNative.IOBackend) (s : State) (i : Input) : IO CryptoBackend := do
  let mut hashes : List (ByteArray × Except CryptoError Digest256) := []
  let mut sigs : List (SignatureRequest × Except CryptoError Bool) := []
  match i with
  | .commit tx q =>
    let mut cfg : Option ContextConfig := none
    let mut isNew := false
    let mut needMessage := false
    match s.transactions tx with
    | some (.pending b) =>
      if b = bindingOf q then
        match s.entries q.key with
        | some (.consumed r) =>
          needMessage := true
          cfg := s.contexts r.pinnedContextVersion
        | some .issued =>
          if s.active q.key.scope = some q.contextVersion then
            cfg := s.contexts q.contextVersion
            isNew := true
        | none => pure ()
    | some (.committed b r _) =>
      if b = bindingOf q then cfg := s.contexts r.pinnedContextVersion
    | _ => pure ()
    if let some c := cfg then
      if InputsFit c.limits c.expected q.signed q.snapshot q.profile then
        needMessage := true
        if isNew then
          if keyOf c.expected = some q.key then
            if let .ok p := prepareVerification c.limits c.expected q.signed q.snapshot q.profile then
              if let some req := p.signatureRequest then
                sigs := [(req, ← backend.verifyEd25519 req.key req.message req.signature)]
              for bytes in p.snapshotRequest.toList ++ p.profileRequest.toList do
                if !(hashes.any (fun h => h.1 = bytes)) then
                  hashes := (bytes, ← backend.sha256 bytes) :: hashes
        else
          for bytes in [q.snapshot, q.profile] do
            if !(hashes.any (fun h => h.1 = bytes)) then
              hashes := (bytes, ← backend.sha256 bytes) :: hashes
    if needMessage then
      let message := (bindingOf q).message
      if !(hashes.any (fun h => h.1 = message)) then
        hashes := (message, ← backend.sha256 message) :: hashes
  | _ => pure ()
  return {
    sha256 := fun b => (lookupMap hashes b).getD (.error .backend_failure)
    verifyEd25519 := fun k m sig =>
      (lookupMap sigs ⟨k, m, sig⟩).getD (.error .backend_failure) }

structure Command where
  image : Image
  input : Input
  deriving FromJson

end ChallengeStore

import tools.challenge_store.Wire

/-! Runtime-only QPM/01 decoding and structural JSON bridge checks.
No new formal round-trip theorem or physical provenance claim. -/
namespace ChallengeStore
open Lean DigitalProvenanceManifestContract DigitalProvenanceReportContract
open DigitalProvenanceChallengeRegistryContract

structure FileManifestInput where
  limits : ManifestLimits
  bytes : ByteArray
  deriving FromJson

structure ManifestBridgeInput extends FileManifestInput where
  manifest : ProvenanceManifestV1
  deriving FromJson

structure FileRequestInput where
  config : ContextConfig
  request : Request
  deriving FromJson

def decodeFileManifest (i : FileManifestInput) : Json :=
  match strictDecodeManifest i.limits i.bytes with
  | none => Json.mkObj [("fileError", toJson "decode_rejected")]
  | some m => Json.mkObj [("manifest", toJson m), ("message", toJson (signingMessageV1 m))]

/-- Compare the manifest received after the actual Python/JSON crossing with a fresh
strict decode of the original bytes, then compare signing bytes as well. -/
def checkManifestBridge (i : ManifestBridgeInput) : Bool :=
  match strictDecodeManifest i.limits i.bytes with
  | none => false
  | some original => decide (original = i.manifest ∧
      signingMessageV1 original = signingMessageV1 i.manifest)

/-- Pre-registration shape/limit check; content refusals remain the registry's job. -/
def fileRequestFits (i : FileRequestInput) : Bool :=
  decide (i.request.signed.signature.size = 64 ∧
    InputsFit i.config.limits i.config.expected i.request.signed i.request.snapshot i.request.profile ∧
    keyOf i.config.expected = some i.request.key)
end ChallengeStore

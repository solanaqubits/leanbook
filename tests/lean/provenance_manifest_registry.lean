import Verification.MasterSuite
open DigitalProvenanceManifestContract
example (r : MasterSuite.VerificationMasterRegistry) (l m) (h : FitsManifestLimits l m) :
    strictDecodeManifest l (encodeManifestV1 m) = some m :=
  r.crypto_suite.provenance_manifest.round_trip l m h
example (r : MasterSuite.VerificationMasterRegistry) (l b m)
    (h : strictDecodeManifest l b = some m) : FitsManifestLimits l m ∧ encodeManifestV1 m = b :=
  r.crypto_suite.provenance_manifest.canonical l b m h
example (r : MasterSuite.VerificationMasterRegistry) : Function.Injective encodeManifestV1 :=
  r.crypto_suite.provenance_manifest.injective
example (r : MasterSuite.VerificationMasterRegistry) : Function.Injective signingMessageV1 :=
  r.crypto_suite.provenance_manifest.signing_injective

import Verification.MasterSuite
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract
example (r : MasterSuite.VerificationMasterRegistry) (l b p e f s x y m) :
    verifyProvenance l b p e f s x y = some (acceptedReport m) ↔
    FitsManifestLimits l m ∧ encodeManifestV1 m = f ∧ ManifestAccepted b p e x y s m :=
  r.crypto_suite.provenance_verifier.exact_acceptance l b p e f s x y m
example (r : MasterSuite.VerificationMasterRegistry) (report : VerificationReport) :
    report.authorization = .blocked := r.crypto_suite.provenance_verifier.blocked report
example (r : MasterSuite.VerificationMasterRegistry) (b p e x y s m)
    (h : ManifestAccepted b p e x y s m) :
    BindingMatches b x m.snapshot ∧ BindingMatches b y m.profile :=
  r.crypto_suite.provenance_verifier.artifact_bindings b p e x y s m h
example (r : MasterSuite.VerificationMasterRegistry) (b p e x y s m)
    (h : ManifestAccepted b p e x y s m) :
    ∃ k, p.lookupKey m.signerId m.keyId = some k ∧
      b.verifyEd25519 k (signingMessageV1 m) s = true :=
  r.crypto_suite.provenance_verifier.signature_message b p e x y s m h

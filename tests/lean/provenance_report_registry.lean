import Verification.MasterSuite
open DigitalProvenanceManifestContract DigitalProvenanceReportContract
example (r : MasterSuite.VerificationMasterRegistry) (a : VerificationReport) :
    a.authorization = .blocked := r.crypto_suite.provenance_report.blocked a
example (r : MasterSuite.VerificationMasterRegistry) (crypto l c s x y)
    (h : ¬ InputsFit l c s x y) :
    verifyProvenance crypto l c s x y = .error .limit_exceeded ∧ plannedRequests l c s x y = [] :=
  r.crypto_suite.provenance_report.preflight_refusal crypto l c s x y h
example (r : MasterSuite.VerificationMasterRegistry) (crypto l c s x y report) :
    verifyProvenance crypto l c s x y = .ok report ↔
    InputsFit l c s x y ∧ executePlan crypto (planVerification c s x y) = report :=
  r.crypto_suite.provenance_report.exact_result crypto l c s x y report
example (r : MasterSuite.VerificationMasterRegistry) (crypto c s x y)
    (h : (executePlan crypto (planVerification c s x y)).signature = .valid) :
    ∃ k, selectKey c s.manifest = .ok k ∧ s.signature.size = 64 ∧
      crypto.verifyEd25519 k.pubKeyBytes (signingMessageV1 s.manifest) s.signature = .ok true :=
  r.crypto_suite.provenance_report.signature_sound crypto c s x y h

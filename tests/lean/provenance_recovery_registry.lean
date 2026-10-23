import Verification.MasterSuite
open DigitalProvenanceReplayContract DigitalProvenanceRecoveryContract

example (suite : MasterSuite.VerificationMasterRegistry) (b s e i r)
    (hr : Reachable b s) (hv : restoreRegistry? e (trusted b s) i = some r) :
    s.acknowledged ⊆ r.usedChallenges :=
  suite.crypto_suite.provenance_recovery.no_ack_loss b s e i r hr hv
example (suite : MasterSuite.VerificationMasterRegistry) (b s i)
    (hr : Reachable b s) (hi : AdmissibleCrashImage b s i) :
    restoreRegistry? b.context (trusted b s) i = some (registryAt b s.committed) :=
  suite.crypto_suite.provenance_recovery.complete b s i hr hi
example (suite : MasterSuite.VerificationMasterRegistry) (b s a c tail e i r q)
    (hr : Reachable b s) (he : (step b s a).emitted = some c)
    (hv : restoreRegistry? e (trusted b (run b (step b s a).state tail)) i = some r)
    (hc : q.expected.challenge = c) : redeemChallenge r q = reject r :=
  suite.crypto_suite.provenance_recovery.emitted_replay b s a c tail e i r q hr he hv hc
example (suite : MasterSuite.VerificationMasterRegistry) (b s a c)
    (hr : Reachable b s) (he : (step b s a).emitted = some c) : c ∈ s.committed :=
  suite.crypto_suite.provenance_recovery.emitted_durable b s a c hr he
example (suite : MasterSuite.VerificationMasterRegistry) (b s xs) (h : Invariant b s) :
    s.anchor <+: (run b s xs).anchor ∧ s.committed <+: (run b s xs).committed ∧
    s.acknowledged ⊆ (run b s xs).acknowledged :=
  suite.crypto_suite.provenance_recovery.monotone b s xs h
example (suite : MasterSuite.VerificationMasterRegistry) (b s q)
    (hf : (redeemChallenge (registryAt b s.committed) q).report = none) :
    prepare b s q = quiet s := suite.crypto_suite.provenance_recovery.refusal b s q hf
example (suite : MasterSuite.VerificationMasterRegistry) (r : Result) :
    r.authorization = .blocked := suite.crypto_suite.provenance_recovery.blocked r

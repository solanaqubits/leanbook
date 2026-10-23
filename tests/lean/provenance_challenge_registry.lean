import Verification.MasterSuite
open DigitalProvenanceChallengeRegistryContract
example (suite : MasterSuite.VerificationMasterRegistry) (crypto inputs) :
    (run crypto initial inputs).accepted.Nodup := suite.crypto_suite.provenance_challenge.unique _ _
example (suite : MasterSuite.VerificationMasterRegistry) (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .newly_consumed r) :
    s.entries q.key = some .issued :=
  (suite.crypto_suite.provenance_challenge.requires_issued crypto s tx q r h).1
example (suite : MasterSuite.VerificationMasterRegistry) (crypto s inputs k r)
    (h : s.entries k = some (.consumed r)) :
    (run crypto s inputs).entries k = some (.consumed r) :=
  suite.crypto_suite.provenance_challenge.immutable crypto s inputs k r h
example (suite : MasterSuite.VerificationMasterRegistry) (crypto s k tx inputs)
    (h : resolve s k tx = .confirmed_not_committed) :
    resolve (run crypto s inputs) k tx = .confirmed_not_committed :=
  (suite.crypto_suite.provenance_challenge.resolution crypto s k tx inputs h).1
example (suite : MasterSuite.VerificationMasterRegistry) (crypto s k tx) :
    (step crypto s (.resolveTransaction k tx)).1 = s :=
  suite.crypto_suite.provenance_challenge.read_only crypto s k tx
example (suite : MasterSuite.VerificationMasterRegistry) (r : ConsumedRecord) :
    r.historicalReport.authorization = .blocked := suite.crypto_suite.provenance_challenge.blocked r
example (crypto s tx first r inputs tx' later) (hk : later.key = first.key)
    (h : (commitChecked crypto s tx first).2 = .newly_consumed r) (r' : ConsumedRecord) :
    (commitChecked crypto (run crypto (commitChecked crypto s tx first).1 inputs) tx' later).2 ≠
      .newly_consumed r' := no_second_new_acceptance crypto s tx first r inputs tx' later h hk r'

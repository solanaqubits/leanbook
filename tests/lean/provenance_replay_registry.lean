import Verification.MasterSuite
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract
open DigitalProvenanceReplayContract

example (suite : MasterSuite.VerificationMasterRegistry) (r q report) :
    (redeemChallenge r q).report = some report ↔ CanRedeem r q report :=
  suite.crypto_suite.provenance_replay.exact_acceptance r q report
example (suite : MasterSuite.VerificationMasterRegistry) (r q)
    (h : checkedReport q = none) : redeemChallenge r q = reject r :=
  suite.crypto_suite.provenance_replay.failure_preserves r q h
example (suite : MasterSuite.VerificationMasterRegistry) (r q)
    (h : (redeemChallenge r q).report = none) : (redeemChallenge r q).registry = r :=
  suite.crypto_suite.provenance_replay.refusal_preserves r q h
example (suite : MasterSuite.VerificationMasterRegistry) (r qs) :
    r.usedChallenges ⊆ (runRequests r qs).usedChallenges :=
  suite.crypto_suite.provenance_replay.history_monotone r qs
example (suite : MasterSuite.VerificationMasterRegistry) (r qs) :
    (runRequests r qs).context = r.context :=
  suite.crypto_suite.provenance_replay.history_context r qs
example (suite : MasterSuite.VerificationMasterRegistry) (r qs q)
    (h : q.expected.challenge ∈ r.usedChallenges) :
    redeemChallenge (runRequests r qs) q = reject (runRequests r qs) :=
  suite.crypto_suite.provenance_replay.replay_rejected r qs q h
example (suite : MasterSuite.VerificationMasterRegistry) (r first rp qs later)
    (h : (redeemChallenge r first).report = some rp)
    (hc : later.expected.challenge = first.expected.challenge) :
    redeemChallenge (runRequests (redeemChallenge r first).registry qs) later =
      reject (runRequests (redeemChallenge r first).registry qs) :=
  suite.crypto_suite.provenance_replay.accepted_replay r first rp qs later h hc
example (suite : MasterSuite.VerificationMasterRegistry) (result : RedemptionResult) :
    result.authorization = .blocked := suite.crypto_suite.provenance_replay.blocked result

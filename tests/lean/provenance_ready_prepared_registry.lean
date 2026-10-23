import Verification.MasterSuite
open DigitalProvenanceReadyPreparedContract

example (suite : MasterSuite.VerificationMasterRegistry) : RecoverySafety :=
  suite.crypto_suite.provenance_ready_prepared.safety
example (suite : MasterSuite.VerificationMasterRegistry) (b) :
    ∃ rel, ForwardSimulation b rel :=
  suite.crypto_suite.provenance_ready_prepared.simulation b
example : ProofObligations := proof_obligations
example (b s i r) (h : Reachable b s) (hv : restoreCandidate? b s i = some r) :
    s.acknowledged ⊆ r.usedChallenges ∧ r.context = b.context :=
  recovery_safety b s i r h hv

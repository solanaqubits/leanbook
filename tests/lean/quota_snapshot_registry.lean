import Verification.MasterSuite
open CryptoHiddenScalarQuotaSnapshotContract
open CryptoHiddenScalarQuotaResumableContract

example : CryptoHiddenScalarQuotaSnapshotContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_snapshot
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaSnapshotContractSuite := r.crypto_suite.quota_snapshot
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaSnapshotContractSuite := r.crypto_full_suite.quota_snapshot
example (r : MasterSuite.VerificationMasterRegistry) {n p j ε}
    (c : QuotaSearchCursor n p j ε) :
    restoreCursor? n p j ε (snapshotCursor c) = some c :=
  r.crypto_suite.quota_snapshot.round_trip n p j ε c

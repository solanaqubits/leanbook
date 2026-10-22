import Verification.MasterSuite
open CryptoHiddenScalarQuotaCanonicalWireContract
open CryptoHiddenScalarQuotaResumableContract

example : CryptoHiddenScalarQuotaCanonicalWireContractSuite := by
  have r := MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
  exact r.crypto_suite.quota_canonical_wire
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoHiddenScalarQuotaCanonicalWireContractSuite := r.crypto_suite.quota_canonical_wire
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoHiddenScalarQuotaCanonicalWireContractSuite := r.crypto_full_suite.quota_canonical_wire
example (r : MasterSuite.VerificationMasterRegistry) (w : QuotaSnapshotWire)
    (s : CryptoHiddenScalarQuotaSnapshotContract.QuotaCursorSnapshot) :
    decodeSnapshotCanonical? w = some s ↔ encodeSnapshotCanonical s = w :=
  r.crypto_suite.quota_canonical_wire.snapshot w s

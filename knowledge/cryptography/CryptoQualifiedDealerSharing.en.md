---
id: CryptoQualifiedDealerSharing
language: en
section: cryptography
source: Verification/CryptoQualifiedDealerSharing.lean
source_sha256: 8f28e9c80f7288997cd4bd3b5328851afeaf0e34b7eb6719e5a760a451b10cc0
novelty: not-assessed
status: reviewed
---

# Aggregation after agreement on qualified dealers

An explicitly fixed finite dealer set determines the sum polynomial, the sum of accepted shares and the public coefficient commitments. A positive threshold and individual degree bounds preserve the aggregate degree bound. Individually verified Feldman shares sum to the aggregate evaluation; two receivers accepting shares at the same coordinate agree. Enough participant coordinates reconstruct the sum of dealer secrets.

Agreement on the qualified set, authenticated commitments and communication are premises outside this algebraic layer. Adding a dealer with a nonzero secret changes the result. Cancelling contribution errors illustrate why aggregate equality does not validate every dealer. This is an aggregation component, not a full DKG or Byzantine agreement proof. Tests exhibit different qualified sets producing different secrets.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [aggregate_degree](../../Verification/CryptoQualifiedDealerSharing.lean#L18)
- [aggregate_eval](../../Verification/CryptoQualifiedDealerSharing.lean#L29)
- [aggregate_commitments](../../Verification/CryptoQualifiedDealerSharing.lean#L33)
- [checked_shares_sum](../../Verification/CryptoQualifiedDealerSharing.lean#L37)
- [receiver_consistency](../../Verification/CryptoQualifiedDealerSharing.lean#L47)
- [qualified_reconstruction](../../Verification/CryptoQualifiedDealerSharing.lean#L55)
- [inserted_dealer_changes_secret](../../Verification/CryptoQualifiedDealerSharing.lean#L66)
- [cancelling_errors](../../Verification/CryptoQualifiedDealerSharing.lean#L74)
- [verification_suite](../../Verification/CryptoQualifiedDealerSharing.lean#L85)

---
id: CryptoPedersenVSSGroup
language: en
section: cryptography
source: Verification/CryptoPedersenVSSGroup.lean
source_sha256: 04b18969e6d5173d2b8bf0ee85a8840837c13b77128a857efa50edb651b7f67c
novelty: not-assessed
status: reviewed
---

# Joint hiding and verified polynomial Pedersen shares

Two polynomials p and r over ZMod q, with prime q and degrees below n, supply message and blinding shares. Coefficient commitments use the existing two-generator prime-order setup. Evaluation commutes with commitments, honest pairs verify, and fixing the blinding evaluation makes the accepted message unique. Two different accepted messages extract the relation between the generators.

The entire vector of coefficient commitments has the uniform distribution when all blinding coefficients are independent uniform field elements. This is a joint-vector theorem, not merely marginal hiding. It excludes observations of private shares. Interpolating accepted pairs opens the constant commitment; it does not unconditionally identify a unique scalar secret. The ZMod 7 tests demonstrate both rejection with fixed blinding and a collision when both openings change. No computational binding, complaint protocol or active-security game is proved.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [evaluation_commutes](../../Verification/CryptoPedersenVSSGroup.lean#L28)
- [honest_completeness](../../Verification/CryptoPedersenVSSGroup.lean#L42)
- [fixed_blinding_soundness](../../Verification/CryptoPedersenVSSGroup.lean#L48)
- [conflicting_shares_extract_relation](../../Verification/CryptoPedersenVSSGroup.lean#L57)
- [coefficient_joint_uniform](../../Verification/CryptoPedersenVSSGroup.lean#L68)
- [coefficient_joint_hiding](../../Verification/CryptoPedersenVSSGroup.lean#L74)
- [verified_reconstruction_commitment](../../Verification/CryptoPedersenVSSGroup.lean#L78)
- [verification_suite](../../Verification/CryptoPedersenVSSGroup.lean#L109)

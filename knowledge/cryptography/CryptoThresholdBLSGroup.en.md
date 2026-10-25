---
id: CryptoThresholdBLSGroup
language: en
section: cryptography
source: Verification/CryptoThresholdBLSGroup.lean
source_sha256: f1a92c9de77005b3489c944dce9343708b72aa82df650a7d28acca9cacd06b25
novelty: not-assessed
status: reviewed
---

# Threshold BLS reconstruction from checked partials

The setup has distinct typed source groups G1 and G2 and a target group with a nondegenerate bilinear map over ZMod q. Partial signatures use shares from one degree-bounded polynomial. Injective participant coordinates and a sufficiently large subset yield the secret-key signature by Lagrange interpolation. If each partial verifies against its honestly generated share public key, the same reconstruction theorem applies to the received partials. Sufficient subsets agree.

The exact aggregate-verification criterion is equality to this signature. No unforgeability, hash-to-curve, subgroup decoding, concrete BN254/BLS12-381 implementation or distributed key-generation protocol is claimed. A zero message group element is explicitly shown to be degenerate. Tests include an insufficient singleton, a wrong signature and a valid two-party reconstruction.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [interpolate_partials](../../Verification/CryptoThresholdBLSGroup.lean#L24)
- [checked_partials_reconstruct](../../Verification/CryptoThresholdBLSGroup.lean#L30)
- [checked_threshold_verifies](../../Verification/CryptoThresholdBLSGroup.lean#L40)
- [quorum_independence](../../Verification/CryptoThresholdBLSGroup.lean#L48)
- [combined_verdict_iff](../../Verification/CryptoThresholdBLSGroup.lean#L56)
- [zero_message_degeneracy](../../Verification/CryptoThresholdBLSGroup.lean#L62)
- [verification_suite](../../Verification/CryptoThresholdBLSGroup.lean#L74)

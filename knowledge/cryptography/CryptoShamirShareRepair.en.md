---
id: CryptoShamirShareRepair
language: en
section: cryptography
source: Verification/CryptoShamirShareRepair.lean
source_sha256: 2b540065bebd0524531638763f06796e4c3eba4a8ce35273b644aa24577c1a0e
novelty: not-assessed
status: reviewed
---

# Repair at arbitrary participant coordinates

For a field, injective participant coordinates and a polynomial of degree below the selected set's cardinality, the repair function interpolates its value at any destination coordinate. Two sufficiently large source sets give the same repaired share. Feldman-verified source shares suffice, assuming injective scalar action on the generator and one fixed commitment vector.

This recovers an arbitrary coordinate rather than just the secret at zero. The repaired share satisfies the original commitment equation. A nonzero weighted contribution error changes the contribution. Tests cover exact finite-field values and failure with only one source for a linear polynomial. The repair messages are not hidden; private repair, communication, availability and malicious-source identification are not modeled.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [repair_evaluations](../../Verification/CryptoShamirShareRepair.lean#L22)
- [repair_verified](../../Verification/CryptoShamirShareRepair.lean#L31)
- [repaired_share_verifies](../../Verification/CryptoShamirShareRepair.lean#L43)
- [repair_quorum_independent](../../Verification/CryptoShamirShareRepair.lean#L52)
- [contribution_error](../../Verification/CryptoShamirShareRepair.lean#L59)
- [verification_suite](../../Verification/CryptoShamirShareRepair.lean#L75)

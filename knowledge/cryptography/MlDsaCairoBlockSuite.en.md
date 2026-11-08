---
id: MlDsaCairoBlockSuite
language: en
section: cryptography
source: Verification/MlDsaCairoBlockSuite.lean
novelty: not-assessed
---

# Cairo block registry

Packages the unchanged arithmetic and arbitrary finite trace theorems from the
four source modules into `CryptoFullSuite.mldsa_cairo`. All canonical-memory,
entry, successful-exit, RangeCheck and rt1 input-binding premises remain explicit.
No real VM correspondence, compiler correctness, execution totality, caller
reachability, FIPS conformance or post-quantum security result is claimed.

[Registry proof](../../Verification/MlDsaCairoBlockSuite.lean#L48).

The `arithmetic_narrow` field records the separate Stage20 composed theorem.
It retains canonical memory, the specified arithmetic trace, numeric AND, the
source-lane bound and checked conversion paths with RangeCheck. Its conclusion
rotates the packed word M[A], not just M[F+25]. The old block fields are unchanged.
[Contract and OPEN register](MlDsaRt1ArithmeticBlock.en.md).

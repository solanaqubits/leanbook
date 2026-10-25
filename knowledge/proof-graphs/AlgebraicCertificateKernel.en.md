---
id: AlgebraicCertificateKernel
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateKernel.lean
source_sha256: 8806aa50939e92f5c1708d48f15c6a83a33bba386e994ba65b98e2589a1e0559
novelty: not-assessed
---

# Rational polynomial certificates

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateKernel.lean)

Defines dimension-indexed sparse polynomials, passports and certificates. A true checkCert result entails zero denotation of the residual. Sparse operations are related to the formal polynomial ring; the result concerns typed data, not external JSON or geometry.

## Interfaces and proof scope

- `exponent`
- `addExponents`
- `add`
- `smul`
- `neg`
- `mulTerm`
- `mul`
- `coefficient`
- `support`
- `active`
- `normalize`
- `normalize_eq_sort`
- `denote_eq_sum_coefficient`
- `denote_normalize`
- `normalize_strict_order`
- `normalize_no_duplicates`
- `normalize_nonzero`
- `Passport`
- `Certificate`
- `combination`
- `residual`
- `isZero`
- `checkCert`
- `denote_flatten`
- `denote_combination`
- `checkCert_sound`
- `eval_soundness`
- `AlgebraicCertificateSuite`
- `verification_suite`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.

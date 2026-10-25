---
id: AlgebraicCertificateNormalizeCached
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateNormalizeCached.lean
source_sha256: a78c415562e1a3a63cfe0b75a6ff138f043703970c3bded45b414592d224bddd
novelty: not-assessed
---

# Coefficient-caching normalization pilot

[Section](README.md) · [Source](../../Verification/AlgebraicCertificateNormalizeCached.lean)

`normalizeCached_eq` proves exact list equality to the production normalizer for
all dimensions and rational sparse inputs. It allows duplicates, zero coefficients
and cancellation; ordering and coefficients are preserved without extra premises.
`denote_normalizeCached` and `checkCert_cached_eq` connect this equality to the
existing denotation and Boolean checker. Production functions are unchanged.

The candidate stores coefficients before filtering and sorting. No asymptotic or
wall-clock bound is proved. The compiled diagnostic and Python reference do not
replace the Lean proof, and this module is not registered in MasterSuite yet.
See the [work package and audit checklist](../../docs/optimization-transfer.en.md).

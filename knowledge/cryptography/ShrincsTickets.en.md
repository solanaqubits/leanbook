---
id: ShrincsTickets
language: en
section: cryptography
source: Verification/ShrincsTickets.lean
source_sha256: 5e312b0b5386676d3b800858bd64e4931b37b55026b0ef8ee573fd1d1c2e8b17
novelty: not-assessed
status: reviewed
---

# Distinct leaves for charged signing events

Two successful single-ticket charges select distinct leaves when the later ledger starts at or above the issued counter after the first charge. Both selections use the same shape and byte-sized depth. The wallet interpretation requires one authoritative ledger per key, durable advancement before signature exposure, and protection against rollback and cloning. The theorem concerns returned leaf coordinates. Cryptographic unforgeability, physical persistence and executable wallet conformance remain open. The registry exposes both the selector and accounting results through `CryptoFullSuite.shrincs_leaves`.

[Theorem](../../Verification/ShrincsTickets.lean#L15)

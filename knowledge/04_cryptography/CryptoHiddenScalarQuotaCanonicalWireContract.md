---
id: CryptoHiddenScalarQuotaCanonicalWireContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaCanonicalWireContract.lean
novelty: not-assessed
status: reviewed
---

# Strict structured canonical quota snapshot codec

Epsilon241, cryptography/bulletproofs-ipa.
[Lean](../../Verification/CryptoHiddenScalarQuotaCanonicalWireContract.lean).

RatWire stores an integer numerator and natural denominator. QuotaSnapshotWire
stores a natural bound and a list of RatWire values. Decoding checks denominator
positivity and coprimality, then constructs Rat.mk' without normalization.
Reducible pairs, noncanonical zero and zero denominators are rejected.

The rational and snapshot decode_iff theorems need no separate canonicality
premise: decode w = some s iff encode s = w. Acceptance is characterized by
canonicality. Both encoders are injective; decoding preserves bound, length,
order and values. Snapshot round trip applies to every typed snapshot, even one
that does not satisfy the context-dependent ValidSnapshot predicate.

restore_encoded_cursor returns the exact original certified cursor.
restore_external_iff separates successful syntax decoding from semantic validity
and the particular cursor's snapshot. Restored continuation is correct for any
requested cap; full cold-result equality requires a nonshrinking bound.
Arbitrary rational profiles and tolerances are allowed.

Proofs use checked Rat.mk' fields, List.mapM induction, Option.some injectivity
and epsilon239 restoration theorems. 29 IO cases and 36 Lean examples including
registry projections cover canonical and malformed pairs, invalid entries at
all list positions, syntax/semantics separation, calibrations4/6 and edge cases.

This is structured data in Lean memory. The existing epsilon240 byte codec and
file reader are preserved. No new byte grammar, profile transfer, provenance,
authorization, cost theorem or physical benchmark is supplied. Only the usual
propext, Classical.choice and Quot.sound are allowed; novelty is not assessed.
This scoped extension is not a new full beta checkpoint.

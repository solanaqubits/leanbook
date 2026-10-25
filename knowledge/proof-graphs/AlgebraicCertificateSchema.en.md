---
id: AlgebraicCertificateSchema
language: en
section: proof-graphs
source: Verification/AlgebraicCertificateSchema.lean
source_sha256: 788538c9486175e41f4764437121b9090dfb2383377d2491f8cc55f81ecfb176
novelty: not-assessed
---

# Typed ALCC schema decoding

[Section](README.md) · [Lean source](../../Verification/AlgebraicCertificateSchema.lean)

Checks exact fields, profile, dimensions, unique identifiers, positional hypothesis matching and canonical rational polynomial terms. Decoding maps terms without normalization. Soundness and relational uniqueness concern typed structures; hash binding and completeness of arbitrary ingestion are separate.

## Interfaces and proof scope

- `bytes`
- `FieldsRel`
- `fields`
- `fields_unique`
- `decimal`
- `signedDecimal`
- `NatRel`
- `IntRel`
- `natChecked`
- `intChecked`
- `nat_unique`
- `int_unique`
- `identifierByte`
- `Identifier`
- `IdentifierRel`
- `identifierChecked`
- `identifier_unique`
- `DigestShape`
- `digestChecked`
- `ItemsRel`
- `itemsChecked`
- `items_unique`
- `items_length`
- `ArrayRel`
- `arrayChecked`
- `array_unique`
- `GoodCoeff`
- `CoeffRel`
- `coeffChecked`
- `coeff_unique`
- `GoodPowers`
- `TermRel`
- `termChecked`
- `term_unique`
- `PolyCanonical`
- `PolyRel`
- `polyChecked`
- `decodePoly`
- `decodePoly_sound`
- `poly_unique`
- `decodePoly_canonical`
- `decodePoly_preserves_terms`
- `WrappedPolyRel`
- `wrappedPolyChecked`
- `wrappedPoly_unique`
- `EntryRel`
- `entryChecked`
- `entry_unique`
- `LiteralRel`
- `literalChecked`
- `passportKeys`
- `certificateKeys`
- `pack`
- `SchemaDecodeRel`
- `schemaChecked`
- `decodeSchema`
- `decodeSchema_sound`
- `schemaDecodeRel_deterministic`
- `items_at`
- `decodePoly_at`
- `decodePoly_length`
- `decodePoly_no_duplicates`
- `term_exact`
- `decodeSchema_unique`

The source types specify the actual hypotheses. See the [ALCC guide](../../docs/alcc.en.md) for execution and trust boundaries. Scientific priority is not assessed.

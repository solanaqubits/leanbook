---
id: MlDsaPackedPredicate
language: en
section: cryptography
source: Verification/MlDsaPackedPredicate.lean
source_sha256: a3e7176ddc8eebbf2fc23cdefbe78173a0ec1fbfb890981d57ee8b4074513944
novelty: not-assessed
status: reviewed
---

# ML-DSA packed coefficient predicate

For five natural coefficients each strictly below 2^23, `pt5 = 0` is equivalent
to all five coefficients being strictly below q = 8380417. The proof decomposes
the sparse mask into lane bits and excludes carries using the 23-bit premises.
It also bounds the packed sum by 2^128 and the Cairo field prime, proves that
three bounded masks cannot cancel modulo that prime, and bounds both unpacked
lanes for arbitrary source words. The explicit 16777215 counterexample shows
that dropping the 23-bit input bound makes the equivalence false.

The development models natural-number bit operations and modular arithmetic.
It does not establish that every Cairo call site satisfies the premises, compiler
refinement, signature unforgeability, constant-time execution or FIPS conformance.

## Provenance and validation

Ported from the frozen ML-DSA-44 Stage 3 arithmetic audit. Original proof bodies
and assumptions are preserved; a license header and a registry suite are added.
The original two modules contain 15 and 55 named theorems respectively. Each
public module adds one packaging theorem. The dependency chain uses Init/Std.
Kernel regressions exercise boundaries, conservative false positives, conditional
repair and registry projections. Axiom auditing checks the imported proof closure;
Cairo measurements belong to a separate experiment and are not Lean results.

## Theorem links

- [and_pow_zero_iff](../../Verification/MlDsaPackedPredicate.lean#L28)
- [mask_decomposition](../../Verification/MlDsaPackedPredicate.lean#L43)
- [mask_zero_iff](../../Verification/MlDsaPackedPredicate.lean#L47)
- [lane_no_carry](../../Verification/MlDsaPackedPredicate.lean#L56)
- [lane_threshold](../../Verification/MlDsaPackedPredicate.lean#L59)
- [packed_fits_u128](../../Verification/MlDsaPackedPredicate.lean#L67)
- [packed_fits_felt](../../Verification/MlDsaPackedPredicate.lean#L75)
- [packed_bits](../../Verification/MlDsaPackedPredicate.lean#L84)
- [pt5_zero_iff](../../Verification/MlDsaPackedPredicate.lean#L97)
- [pt5_le_mask](../../Verification/MlDsaPackedPredicate.lean#L107)
- [three_masks_no_cancellation](../../Verification/MlDsaPackedPredicate.lean#L110)
- [counterexample_without_23_bit_premise](../../Verification/MlDsaPackedPredicate.lean#L123)
- [window_le_mask](../../Verification/MlDsaPackedPredicate.lean#L130)
- [unpack8_low_bounded](../../Verification/MlDsaPackedPredicate.lean#L151)
- [unpack8_high_bounded](../../Verification/MlDsaPackedPredicate.lean#L179)
- [verification_suite](../../Verification/MlDsaPackedPredicate.lean#L226)

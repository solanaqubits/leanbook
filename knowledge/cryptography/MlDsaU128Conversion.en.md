---
id: MlDsaU128Conversion
language: en
section: cryptography
source: Verification/MlDsaU128Conversion.lean
source_sha256: cee8be432db3005edf80433d7f963e5e11deb01a4bb8bcdf229dbf5800349617
novelty: not-assessed
status: locally-verified-numeric-conversion
---

# Numeric u128 conversion constraints and rt1 composition

This module models the scalar constraints of the two branches of
u128s_from_felt252, manually extracted from Cairo 2.18.0 commit
8746d71d04ca94bb392206bbfc21bcb257d7930a. It imports MlDsaRt1 unchanged.
It does not define a Cairo/CASM machine semantics.

Let U=2^128, P=MlDsaRt1.cairoPrime, and A=maxHigh=(P-1)/U.
WideChecks requires a canonical r, x,y<U, (x*U+y)%P=r, nonzero x,
and the adjusted residue range check: (y+U-1)%P<U if x=A,
or (x+U-A)%P<U otherwise. The ordinary equality r=x*U+y is derived,
not inserted as an assumption in WideChecks.

The adjusted checks are equivalent to x<A or (x=A and y=0), under the
limb bounds. They therefore force canonical recomposition below P.
Nonzero x then implies r>=U. For r<U the numeric conversion relation
has exactly the outcome Narrow(r). The rt1 arithmetic theorem composes
with this relation to give Narrow(packRotl64_1 w), and its Option view
is Some of the packed rotation, for every w<2^128 and the exact mask.
The original rt model at pow=2 has the same admissible outcome.

## Validation

14 named theorems; strict compile and scoped Lake build pass. The final
standard CLI audit covers 98 declarations including the imported arithmetic
module and generated declarations, with only propext, Quot.sound and
Classical.choice, no violations or sorryAx. There is no independent second
auditor run. No native_decide is used. All 27 boundary examples pass.

The examples include valid Narrow at zero/U-1, valid Wide at U/P-1, incorrect
returned values, and counterexamples when adjusted canonicality or nonzero-high
checks are removed. For x=A,y=1, modular recomposition is zero despite x!=0.

## Scope and open bridge

Satisfiability and uniqueness of this numeric relation are not VM termination.
Narrow preserves its input by definition of the relation, following the source
branch output; the real branch's value-flow refinement is not proved here.
The source-to-relation translation, memory and RangeCheck semantics, hint
execution, gas, compiler/USC provenance, actual CASM artifact and full verifier
correctness remain open. No FIPS or cryptographic/quantum security claim follows.

Historical local evidence (not included in this public export).
Historical local evidence (not included in this public export).
Public integration retains the exact checked mathematical source.

## Theorems

- [prime_eq_maxHigh_mul_bound_add_one](../../Verification/MlDsaU128Conversion.lean#L24)
- [bound_constants](../../Verification/MlDsaU128Conversion.lean#L28)
- [high_is_max_iff](../../Verification/MlDsaU128Conversion.lean#L33)
- [wideRangeCheck_iff](../../Verification/MlDsaU128Conversion.lean#L53)
- [wideChecks_recomposition](../../Verification/MlDsaU128Conversion.lean#L60)
- [wideChecks_iff](../../Verification/MlDsaU128Conversion.lean#L69)
- [wideChecks_ge_bound](../../Verification/MlDsaU128Conversion.lean#L86)
- [not_wideChecks_of_lt](../../Verification/MlDsaU128Conversion.lean#L94)
- [conversionChecks_lt_iff](../../Verification/MlDsaU128Conversion.lean#L113)
- [narrowChecks_exists](../../Verification/MlDsaU128Conversion.lean#L131)
- [rt1_conversionChecks_iff](../../Verification/MlDsaU128Conversion.lean#L136)
- [rt1_not_wide](../../Verification/MlDsaU128Conversion.lean#L144)
- [rt1_resultOption_eq_some](../../Verification/MlDsaU128Conversion.lean#L156)
- [rt_pow2_conversionChecks_iff](../../Verification/MlDsaU128Conversion.lean#L163)

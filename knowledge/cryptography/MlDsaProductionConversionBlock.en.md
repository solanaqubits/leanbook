---
id: MlDsaProductionConversionBlock
language: en
section: cryptography
source: Verification/MlDsaProductionConversionBlock.lean
source_sha256: ca0d92465aac3d3db8e4e4ee8f6127a19622aad4e203a7a9298bdf860671d1e5
novelty: not-assessed
status: locally-verified-block-assertion-bridge
---

# Pinned production conversion block: conditional assertion bridge

Stage15 production CASM SHA-256 4b817187ccc55e73f3837d5995e2dfb761217f898aa43359c323783cfa4e09e3,
compiler_version 2.18.0, contains the selected conversion template at PCs
1274 through 1296: 14 instructions and 23 words. Narrow exits to PC1297;
Wide exits to PC1309. This is production Scarb output, not USC diagnostic output.
The block's caller and its connection to a particular rt1 invocation are unknown.

The module embeds the literal words, checks their encoded fields and relative
jump targets with kernel-evaluated proofs, and formalizes intermediate scalar
cell assertions for both successful exits. The Wide relation includes separate
shifted, difference and checked cells. Those equations imply WideChecks; any
ExitAssertions result implies ConversionChecks. The failure assertion at PC1294
is numerically inconsistent for a canonical field value.

Composition with rt1 requires the explicit premise that the block input equals
rt1FieldExpr w rt1Mask, plus w<2^128 and a successful ExitAssertions outcome.
It concludes Narrow(packRotl64_1 w), or Some of that value in the numeric Option
view. It does not assert such a production rt1 caller is identified or reachable.

## Validation

10 named theorems, strict elaboration and scoped Lake build passed. The standard
CLI audits 142 declarations in the project import closure, including generated
ones, with propext, Classical.choice and Quot.sound; zero violations, no sorryAx
or native_decide. All 20 focused Lean examples passed. Seven mutated extraction
certificates were rejected (word, operand, immediate, jump, hint, boundary, AP delta).
The Python checker is not an independent formal auditor.

## Trust boundary

A hash-pinned Python extractor ties the JSON artifact to the literal words and
checks the prefix's instruction starts under its decoder. This decoder is not
verified; linear decoding is not a reachability proof. Encoded field checks in
Lean do not certify general opcode execution semantics. The interpretation of
AP/FP progression, immutable memory, canonical field arithmetic, RangeCheck and
output bindings as ExitAssertions is manual and explicit. There is no VM,
compiler, hint-execution, resource-totality or whole-verifier security theorem.

Historical local evidence (not included in this public export).
Historical local evidence (not included in this public export).
Public integration retains the exact checked mathematical source.

## Theorems

- [decoded_fields_exact](../../Verification/MlDsaProductionConversionBlock.lean#L47)
- [block_sizes](../../Verification/MlDsaProductionConversionBlock.lean#L52)
- [immediate_words_exact](../../Verification/MlDsaProductionConversionBlock.lean#L55)
- [relative_targets_exact](../../Verification/MlDsaProductionConversionBlock.lean#L62)
- [wideAssertions_to_checks](../../Verification/MlDsaProductionConversionBlock.lean#L99)
- [exitAssertions_to_checks](../../Verification/MlDsaProductionConversionBlock.lean#L118)
- [failure_assert_impossible](../../Verification/MlDsaProductionConversionBlock.lean#L129)
- [no_wide_assertions_of_lt](../../Verification/MlDsaProductionConversionBlock.lean#L135)
- [rt1_exit_is_narrow](../../Verification/MlDsaProductionConversionBlock.lean#L141)
- [rt1_exit_option](../../Verification/MlDsaProductionConversionBlock.lean#L149)

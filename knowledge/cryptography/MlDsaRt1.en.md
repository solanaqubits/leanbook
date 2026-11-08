---
id: MlDsaRt1
language: en
section: cryptography
source: Verification/MlDsaRt1.lean
source_sha256: 4c71d1dbc65b670c7ff96363019ce4c2f7a9a16b7833b069dd9e33e65c18d2a0
novelty: not-assessed
status: locally-verified-arithmetic
---

# ML-DSA rt1 arithmetic correspondence

For every natural w < 2^128 and the exact rt1Mask, the canonical natural residue
model rt1FieldExpr w rt1Mask equals two independent rotate-left-by-one operations
on its 64-bit halves, packed into a result below 2^128. The original rt model
at pow=2 has the same result. The earlier equality between the two field models
continues to hold for all natural inputs and arbitrary masks.

The proof extracts masked remainder/quotient halves using Nat.and_mod_two_pow
and Nat.and_div_two_pow, derives a division-free linear identity, and proves the
canonical residue equality using exact numeric constants. It needs neither a
primality hypothesis nor a compiler-refinement assumption. Primality of P is not
proved by this module. Natural subtraction is padded before subtracting a residue.

The external NotebookLM fragment left an unsolved testBit goal. Its intermediate
single-lane scaled identity omitted a factor 2^63; a kernel-checked counterexample
preserves this lesson. The final packed identity was correct and is proved unchanged.

## Actual validation

Lean 4.33.1, only Init/Std. Scoped Lake build and strict re-elaboration pass.
The standard verifier CLI audits 39 declarations with only propext and Quot.sound,
zero violations; 17 named theorems, 25 separately compiled Lean examples. There
is no separate independent-auditor run, no native_decide and no new custom axiom.
Counterexamples demonstrate that the input bound and exact mask are essential.

Historical local evidence (not included in this public export).
Historical local evidence (not included in this public export)
is pinned to previous commit e2711ba8166d9a09eccef03136cc6504ffa3513b.

## Provenance and open implementation bridge

Stage15 job mj_51c7a1c99b6f41ee96bc62c13b950396; patch SHA-256
cfbe31ae486aca6f79954b154d78da9a5be4190731c53064caf633b00cf4c155.
k2.cairo SHA-256 6c675fefa1530cb855567c6261241b22b0fde2a4623b363878c1f31f98755540.
rt lines4–8 and rt1 lines10–15 were mapped manually into the models.

Cairo libfunc semantics, all actual call-site premises, Narrow/Wide execution,
compiler/runtime correspondence, FIPS conformance and whole-signature or quantum
security remain unproved. The public registry records bounded arithmetic obligations, not a full-verifier certificate.

## Theorems

- [low64_lt](../../Verification/MlDsaRt1.lean#L42)
- [high64_lt](../../Verification/MlDsaRt1.lean#L46)
- [rotl64_1_lt](../../Verification/MlDsaRt1.lean#L51)
- [packRotl64_1_lt_u128](../../Verification/MlDsaRt1.lean#L56)
- [dConstant_eq_two_cConstant](../../Verification/MlDsaRt1.lean#L64)
- [cairoPrime_pos](../../Verification/MlDsaRt1.lean#L67)
- [constants_lt_modulus](../../Verification/MlDsaRt1.lean#L70)
- [dConstant_mul_half_mod](../../Verification/MlDsaRt1.lean#L74)
- [residue_le_padded](../../Verification/MlDsaRt1.lean#L78)
- [rt1_eq_rt_pow2](../../Verification/MlDsaRt1.lean#L95)
- [rt1Mask_eq_sum](../../Verification/MlDsaRt1.lean#L102)
- [and_bit63_of_lt](../../Verification/MlDsaRt1.lean#L105)
- [land_rt1Mask_eq](../../Verification/MlDsaRt1.lean#L118)
- [packRotl64_1_linear_identity](../../Verification/MlDsaRt1.lean#L135)
- [rt1FieldExpr_eq_packRotl64_1](../../Verification/MlDsaRt1.lean#L143)
- [rt1FieldExpr_eq_packRotl64_1_and_lt](../../Verification/MlDsaRt1.lean#L155)
- [rtFieldExpr_pow2_eq_packRotl64_1](../../Verification/MlDsaRt1.lean#L160)

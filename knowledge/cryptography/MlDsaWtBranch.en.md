---
id: MlDsaWtBranch
language: en
section: cryptography
source: Verification/MlDsaWtBranch.lean
source_sha256: 365fafc2f3b0df4a2b1fd15f887abae1211a424636ac9499a9d4e0214ae05df4
novelty: not-assessed
status: reviewed
---

# ML-DSA conservative word tests and conditional repair

The word test is `(w + k) &&& t`. Two-lane decomposition requires the explicit
no-carry premise `lo + k < 2^64` and mask bound `t < 2^64`. The three layouts
have separate width premises. Coarse checks for split coefficients are sound
but conservative: valid coefficients can trigger the slow path. The module
characterizes those false positives instead of claiming exact q comparison.

For lists of at most 21 bounded contributions, the low 71-bit sum is exact.
Prefix differences additionally require their stated field/no-wrap bounds.
The low and high repair equivalences retain `hclear : part = 0 → valid` as a
hypothesis; the actual Cairo slow-path predicate is not instantiated here.
Filtering preserves the list only when every coefficient is below q = 8380417.

These are arithmetic model proofs, not an end-to-end proof of the optimized
Cairo program, its compiler, Keccak, ML-DSA security or constant-time behavior.

## Provenance and validation

Ported from the frozen ML-DSA-44 Stage 3 arithmetic audit. Original proof bodies
and assumptions are preserved; a license header and a registry suite are added.
The original two modules contain 15 and 55 named theorems respectively. Each
public module adds one packaging theorem. The dependency chain uses Init/Std.
Kernel regressions exercise boundaries, conservative false positives, conditional
repair and registry projections. Axiom auditing checks the imported proof closure;
Cairo measurements belong to a separate experiment and are not Lean results.

## Theorem links

- [and_lanes](../../Verification/MlDsaWtBranch.lean#L16)
- [wt_lanes](../../Verification/MlDsaWtBranch.lean#L27)
- [wt_lanes_zero_iff](../../Verification/MlDsaWtBranch.lean#L38)
- [low_bit](../../Verification/MlDsaWtBranch.lean#L47)
- [high_bit](../../Verification/MlDsaWtBranch.lean#L52)
- [byte_threshold](../../Verification/MlDsaWtBranch.lean#L56)
- [halfword_threshold](../../Verification/MlDsaWtBranch.lean#L63)
- [lane0_fits](../../Verification/MlDsaWtBranch.lean#L75)
- [lane0_offset](../../Verification/MlDsaWtBranch.lean#L82)
- [lane0_bit0](../../Verification/MlDsaWtBranch.lean#L89)
- [lane0_bit1](../../Verification/MlDsaWtBranch.lean#L97)
- [mask0_decomposition](../../Verification/MlDsaWtBranch.lean#L108)
- [mask0_zero_iff](../../Verification/MlDsaWtBranch.lean#L110)
- [wt0_lane_zero_iff](../../Verification/MlDsaWtBranch.lean#L115)
- [source_constants_0](../../Verification/MlDsaWtBranch.lean#L122)
- [lane1_fits](../../Verification/MlDsaWtBranch.lean#L131)
- [lane1_offset](../../Verification/MlDsaWtBranch.lean#L138)
- [lane1_bit0](../../Verification/MlDsaWtBranch.lean#L145)
- [lane1_bit1](../../Verification/MlDsaWtBranch.lean#L153)
- [lane1_bit2](../../Verification/MlDsaWtBranch.lean#L164)
- [mask1_decomposition](../../Verification/MlDsaWtBranch.lean#L178)
- [mask1_zero_iff](../../Verification/MlDsaWtBranch.lean#L180)
- [wt1_lane_zero_iff](../../Verification/MlDsaWtBranch.lean#L185)
- [source_constants_1](../../Verification/MlDsaWtBranch.lean#L192)
- [lane2_fits](../../Verification/MlDsaWtBranch.lean#L201)
- [lane2_offset](../../Verification/MlDsaWtBranch.lean#L208)
- [lane2_bit0](../../Verification/MlDsaWtBranch.lean#L215)
- [lane2_bit1](../../Verification/MlDsaWtBranch.lean#L223)
- [lane2_bit2](../../Verification/MlDsaWtBranch.lean#L234)
- [mask2_decomposition](../../Verification/MlDsaWtBranch.lean#L248)
- [mask2_zero_iff](../../Verification/MlDsaWtBranch.lean#L250)
- [wt2_lane_zero_iff](../../Verification/MlDsaWtBranch.lean#L255)
- [source_constants_2](../../Verification/MlDsaWtBranch.lean#L262)
- [masked_word0_fits](../../Verification/MlDsaWtBranch.lean#L266)
- [masked_word1_fits](../../Verification/MlDsaWtBranch.lean#L272)
- [masked_word2_fits](../../Verification/MlDsaWtBranch.lean#L278)
- [split_c2_sound](../../Verification/MlDsaWtBranch.lean#L284)
- [split_c5_sound](../../Verification/MlDsaWtBranch.lean#L288)
- [split_c2_false_positive_iff](../../Verification/MlDsaWtBranch.lean#L292)
- [split_c5_false_positive_iff](../../Verification/MlDsaWtBranch.lean#L296)
- [conservative_not_exact](../../Verification/MlDsaWtBranch.lean#L300)
- [wt_low_bound](../../Verification/MlDsaWtBranch.lean#L306)
- [source_masks_low_bound](../../Verification/MlDsaWtBranch.lean#L315)
- [sum_bounded](../../Verification/MlDsaWtBranch.lean#L321)
- [sum_fits_felt](../../Verification/MlDsaWtBranch.lean#L332)
- [low_sum_fits](../../Verification/MlDsaWtBranch.lean#L340)
- [sum_mod_map](../../Verification/MlDsaWtBranch.lean#L353)
- [low_sum_exact](../../Verification/MlDsaWtBranch.lean#L360)
- [af_u128_projection](../../Verification/MlDsaWtBranch.lean#L368)
- [low_prefix_equal_iff](../../Verification/MlDsaWtBranch.lean#L374)
- [high_clear_iff](../../Verification/MlDsaWtBranch.lean#L382)
- [field_prefix_difference](../../Verification/MlDsaWtBranch.lean#L386)
- [repair_low_exact](../../Verification/MlDsaWtBranch.lean#L399)
- [repair_high_exact](../../Verification/MlDsaWtBranch.lean#L413)
- [filter_identity](../../Verification/MlDsaWtBranch.lean#L430)
- [verification_suite](../../Verification/MlDsaWtBranch.lean#L463)

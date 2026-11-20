---
id: ShrincsLeaf
language: en
section: cryptography
source: Verification/ShrincsLeaf.lean
source_sha256: fb440388c19d21cdda4c83c498dbf608d37835164e5fc19e863dc2731ec84eb5
novelty: not-assessed
status: reviewed
---

# FXMSS leaf selection

For a fixed shape and depth at most 255, two successful selections returning the same pair (index, height) have equal counters. Balanced trees encode the counter in the index. Unbalanced trees reuse index 1 at different heights and end with a leaf at index 0. Missing counters, depth zero and unknown shapes produce no leaf. The proof ranges over natural counters, which include all representable UInt64 inputs.

[Theorem](../../Verification/ShrincsLeaf.lean#L47)

The [reference selector](https://github.com/SHRINCS/shrincs-bip/blob/ad93be730f0a774631b4e8aac9905f0071b1276b/impl/shrincs.py#L1581-L1624)
was compared with the executable Lean definition on 43,305 inputs. The comparison
covers all usable unbalanced leaves, small balanced trees, byte depths 0–255
and selected UInt64 boundaries. To reproduce from the repository root, build
`Verification.ShrincsLeaf` and run `python3 tests/shrincs/compare.py /path/to/impl/shrincs.py`
with the pinned reference file. The script checks its SHA-256 before loading it.
General Python-to-Lean equivalence and custom tree rules are outside the theorem.

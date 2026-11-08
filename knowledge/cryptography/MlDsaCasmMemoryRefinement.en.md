---
id: MlDsaCasmMemoryRefinement
language: en
section: cryptography
source: Verification/MlDsaCasmMemoryRefinement.lean
source_sha256: 354fa3b1a4391df0f301f1f82f57e3828c1021ed575dbe3dc8e5db26957ddee5
novelty: not-assessed
status: locally-verified-forward-memory-refinement
---

# Forward refinement of abstract segmented memory

The model uses Nat segment identifiers, checked signed offsets, typed felt/pointer
values and a common immutable partial memory. Temporary negative segments,
allocation and deduction of unknown operands are not modeled. No concrete Cairo
VM repository or revision is pinned by this module.

`RelocatesTo` explicitly supplies a canonical flat realization of every defined
cell. Existence of this realization is not proved. `NonAliasing` is a separate
optional predicate, not a necessary-and-sufficient construction criterion.
Write-once extensions preserve existing cells; restriction of a supplied final
realization to an earlier partial memory is proved.

`CodeRead` constrains actual program words and immediates to the inherited pinned
block. `SegStep` uses typed reads, scalar arithmetic and checked address changes;
it does not assume a flat Step or ExitAssertions. PC projects to the program
offset while AP and FP use relocation bases. `step_projection` derives the flat
step; `trace_projection` lifts this to arbitrary finite lists.

With the specified entry and exit conditions, `trace_projection_classification`
and `segmented_trace_lengths` reuse Stage16c to give three projected paths and
3/12/11 states. Typed RangeCheck conditions produce ExitAssertions and
ConversionChecks. `trace_projection_rt1` additionally assumes w<2^128 and that
the block input equals rt1FieldExpr. Exits mark the modeled window, not VM halt.

## Verification

23 named theorems and 24 examples passed strict compilation and scoped Lake build.
The standard CLI audited 514 declarations in the imported project closure, with
zero violations and only propext, Classical.choice and Quot.sound. No sorryAx or
native_decide. One fresh build target appeared in the 799-job dependency graph;
this is not a fresh whole-library build or an independent second audit.

Examples cover offset underflow, felt/pointer distinctions, invalid pointer
images, conflicting write-once values, relocation collisions, incorrect program
segments and a concrete two-step Narrow trace with its RangeCheck witness.
Three earlier attempts failed; the explicitly authorized fourth passed after a
line-wrap correction. Peak cgroup memory was 382050304 bytes (~364 MiB), no OOM.

## Open scope

This proves forward preservation of an abstract typed memory witness under explicit
compatibility assumptions. Reverse lifting, operand deduction and allocation,
actual Cairo VM correspondence, production reachability and rt1 caller attribution,
compiler correctness, full ML-DSA/FIPS correctness and quantum security remain open.
No MasterSuite/root-import integration or push was performed.

[Public integration record](../../docs/rt1-stage20-public.md).
[Historical summary](../../docs/rt1-stage20/rt1-stage20-public/historical-summary.json).

## Public synchronization

The preceding validation counts describe the local research checkpoint.
[New public-tree checks and exclusions](../../docs/rt1-stage20-public.md) are recorded separately.

Stage 17 attributed the old PC1274–1296 window to `tx_version`. Its conditional
rt1 lemmas do not identify an actual rt1 caller. The new PC3625–3663 candidate
has separate path theorems; old completeness and memory results do not transfer.

---
id: MlDsaCasmWitnessLifting
language: en
section: cryptography
source: Verification/MlDsaCasmWitnessLifting.lean
source_sha256: 3ad62f11d3f67093f0a32b1660e34e0df5c5044aa5aaa4228734143c7af655bf
novelty: not-assessed
status: locally-verified-three-path-witness-lifting
---

# Witness lifting for all three conversion-block paths

Stage16e constructs compatible typed witnesses for Narrow, WideEqual and WideLess
in the abstract segmented-memory model. The original Narrow definitions and proofs
and all five imported project modules are unchanged.

## Witnesses and constructed memory

`NarrowWitness` retains its seven-cell footprint and scalar input v<2^128.
`Wide.Witness` contains numeric data and layout assumptions only: high/low words
below 2^128, nonzero high, explicit modular equations for the input and three
intermediate scalars, and the equal/less branch condition relative to maxHigh.
The equal branch requires high=maxHigh and low=0; the less branch requires
high<maxHigh. `WideEqualWitness` and `WideLessWitness` select that Boolean branch.
No SegStep, SegCheckedTrace, projected-path equality or flat realization is assumed.

All witnesses use distinct Nat code/execution/RC segments, AP offset a+1 and
FP offset f+5, a canonical nonnegative relocated RC pointer, and relocation
injectivity on their finite footprint. These are sufficient layout restrictions,
not necessary or minimal conditions for arbitrary VM executions.

Wide memory has 34 assignments: 23 pinned code words, one typed RC pointer at
FP-5, seven stack scalars (input at AP-1, zero selector, shifted high, high-minus-A,
adjusted RC scalar, high and low), and three RC scalars. Initial memory contains
code, pointer and input. Ready memory adds nine scalar cells and preserves every
initial assignment. Outside the footprint memory is undefined. Repeated assertion
of an identical value is permitted. Address injectivity excludes conflicting
assignments in this construction.

The finite memory construction uses Classical.choose. Every scalar needed by a
step is prepared before the trace begins. This proves defined, typed reads from
completed partial memory, not an executable hint solver, dynamic allocation,
operand deduction or a chronology of initially unknown writes.

## Verified API and paths

- Existing Narrow API derives PC1274 -> PC1296 -> PC1297, with one RC slot.
- `Wide.extends_initial`, `initial_at`, `prepared_initially_absent` and
  `assignment_consistent` establish preservation and assignment compatibility.
- `Wide.stack_read`, `ptr_read`, `rc_read` and instruction-specific lemmas supply
  operand typing and derive each SegStep directly from the independent rules.
- `Wide.equal_checked` and `less_checked` derive the 12-state and 11-state traces,
  respectively, both exiting at PC1309. Their prefixes/tails follow Stage16c.
- `Wide.equal_projection` and `less_projection` prove project-after-lift equality
  with the respective canonical flat path.
- `Wide.relocates` constructs the canonical flat memory; `rangeChecks` proves
  all three RC slots. `equal_flat_checked` and `less_flat_checked` compose Stage16d.
- `Wide.equal_exitAssertions` and `less_exitAssertions` compose the lifted
  execution with Stage16d/16c to obtain ExitAssertions; existing conversion
  theorems then apply.

This is a conditional retraction for compatible typed witnesses, not a converse
for every arbitrary flat-memory execution.

## Verification

The final unchanged source passed strict compilation, scoped Lake build and the
standard CLI transitive axiom audit: **73 named theorems, 41 examples, 871 project
closure declarations**, no violations, no sorryAx or native_decide; axioms are
propext, Classical.choice and Quot.sound. The extension adds 54 theorems and
25 examples. One fresh target in the 800-job graph is not a whole-library rebuild.

Concrete Wide witnesses cover input P-1 (equal), 2^128 (minimum less) and P-2
(maximum less), all three RC slots, projection, exit PCs, initial absence of
prepared cells, pointer/scalar mismatch, overlapping frame slots, zero high and
an incorrect intermediate scalar. Existing 16 Narrow examples are retained.

The final run took 18.669s with cgroup peak 456396800 bytes (~435 MiB). Earlier
Wide development encountered kernel memory failures and timeouts; those logs are
retained. The largest observed Wide peak was 6150770688 bytes (~5.73 GiB), below
the 8 GiB cgroup cap, with no Docker OOM kill. Explicit intermediate scalar fields
with arithmetic equations avoided expensive repeated reduction inside typed reads.
No strict checks were disabled. The original Lake configuration was restored.

## Boundaries and evidence

The external Cairo VM revision, real runtime/deduction/hints, temporary negative
segments, production reachability, rt1 caller attribution, compiler and full
ML-DSA/FIPS correctness remain open. No main, Quantum, SimLab or MasterSuite
integration or publication was performed by this work.

[Public integration record](../../docs/rt1-stage20-public.md).
[Historical summary](../../docs/rt1-stage20/rt1-stage20-public/historical-summary.json).
[Historical summary](../../docs/rt1-stage20/rt1-stage20-public/historical-summary.json).
[Public integration record](../../docs/rt1-stage20-public.md).
The historical Narrow manifest pins commit 4428b4d and is not a manifest of this
extended source; the new wide-manifest.sha256 records the current artifacts.

## Public synchronization

The preceding validation counts describe the local research checkpoint.
[New public-tree checks and exclusions](../../docs/rt1-stage20-public.md) are recorded separately.

Stage 17 attributed the old PC1274–1296 window to `tx_version`. Its conditional
rt1 lemmas do not identify an actual rt1 caller. The new PC3625–3663 candidate
has separate path theorems; old completeness and memory results do not transfer.

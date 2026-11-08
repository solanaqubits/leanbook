---
id: MlDsaRt1ConversionBlock
language: en
section: cryptography
source: Verification/MlDsaRt1ConversionBlock.lean
source_sha256: 58ac1f4ab48d8282a1e798a824c3bb36d5e52a7f8838cc722b9a21d83ae77c1b
novelty: not-assessed
status: locally-verified-candidate-conversion-paths
---

# Candidate rt1 conversion: new pinned instruction paths

Stage 19 applies the existing decoded-instruction semantics to the candidate
production window PC3641..3663 (23 words, 14 instructions). All six predecessor
Lean modules remain byte-identical. The direct import is MlDsaCasmBlockSemantics;
its four-module predecessor closure supplies the arithmetic/conversion foundations.

## New addresses, independent steps and hypotheses

The new literal words and all 14 closed fetch/decode results are checked by the
Lean kernel. A separate fetch/Step/CheckedTrace uses the inherited DecodedStep
rules, not the old block's fetch or address-specific theorems. The input cell is
entryAP-4. The RC pointer is read at entryAP-24, and RC slots start at pointer+1.
Other intermediate/high/low cells are at AP+1 through AP+5; selector is at AP.

The three explicit paths are Narrow (3 states, exit3664), WideEqual (12 states,
exit6509) and WideLess (11 states, exit6509). `BlockExecution` requires only their
checked steps, separate RangeCheck bounds and numeric output bindings. It does
not assume ExitAssertions or ConversionChecks. Canonical completed flat memory
is an additional premise of the soundness theorems. Hints need not be trusted:
a successful path must satisfy the instruction assertions and supplied RC bounds.

## Results

- `execution_to_exitAssertions` derives intermediate scalar constraints from the
  NEW steps; the old scalar assertion relation is reused only after this derivation.
- `execution_to_conversionChecks` yields the numeric conversion contract.
- `no_failure_step` rules out the explicit contradictory assertion at 3661.
- `execution_rt1_narrow` and `execution_rt1_option` compose with rt1 arithmetic,
  conditional on w<2^128 and input=rt1FieldExpr w rt1Mask.
- `rt1_no_wide_path` excludes both modeled Wide paths under that input equation.
- `wide_paths_end_6509` and `external_fetch_none` identify the local boundary.
  No semantics of code at 6509 or behavior after that boundary is asserted.

The Wide numeric tag describes an outgoing high/low pair, not successful return
from an enclosing Cairo function. Likewise, the Option view is arithmetic; it
is not a proof that real unwrap/panic code executes in a particular way.

## Verification

48 named theorems and 26 examples. Strict compile, scoped Lake build and standard
CLI transitive audit passed:461 project closure declarations, zero violations,
no sorryAx or native_decide; permitted axioms propext, Classical.choice, Quot.sound.
One fresh target in an 799-job graph, not a whole-library check. The smaller closure
than Stage 16e reflects a narrower import graph, not removal of prior results.

Examples construct both Wide paths and both endpoint Narrow values, check the new
word fields/exits, reject incorrect outputs, zero-high Wide, high=maxHigh/low=1,
and out-of-range Narrow without RangeCheck. The last pair demonstrates that the
RC premise is essential. No new external VM executions were performed.

The final verifier took 19.343s with peak 393592832 bytes (~375 MiB), Docker OOM=0.
The first attempt failed only a strict long-comment linter; it was corrected
without disabling checks. Lake's temporary memory option was restored.

## Boundaries

This closes explicit finite-path soundness for the new conversion block only.
Arbitrary-trace classification, the Stage 18 arithmetic window's memory/dataflow
proof, input equality, actual Bitwise-segment membership, exact source/inline
attribution, real VM/segmented runtime and reachability remain open. Prior Stage 16c
classification is not automatically transferred to this new fetch window.
PC 6509 is an external endpoint, not a proved panic or VM halt. No main, Quantum,
SimLab, MasterSuite integration, push or publication was performed.

[Stage 19 report](../../docs/rt1-stage20/RT1_CONVERSION_STAGE19.md).
[Historical summary](../../docs/rt1-stage20/rt1-stage20-public/historical-summary.json).
[Historical summary](../../docs/rt1-stage20/rt1-stage20-public/historical-summary.json).

## Public synchronization

The preceding validation counts describe the local research checkpoint.
[New public-tree checks and exclusions](../../docs/rt1-stage20-public.md) are recorded separately.

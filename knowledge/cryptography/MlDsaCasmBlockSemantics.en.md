---
id: MlDsaCasmBlockSemantics
language: en
section: cryptography
source: Verification/MlDsaCasmBlockSemantics.lean
source_sha256: a091865ee00e6a71071159bd17d9736da2d49881452a2fa583104abdd3518be5
novelty: not-assessed
status: locally-verified-arbitrary-finite-trace-classification
---

# Complete finite-trace classification of the pinned conversion block

Stage16b introduced instruction semantics and checked three explicit paths for
production CASM PCs1274–1296. Stage16c extends the same module without changing
any earlier declaration body. Its theorem now quantifies over an arbitrary
finite list of states; no fuel, length bound or path membership is assumed.

## Statement and composition

`TraceCompleteness.trace_classification` assumes canonical immutable memory,
entry state PC1274/AP=a/FP=f, `CheckedTrace` for adjacent instruction steps, and
`EndsAtExit`. The endpoint predicate is proved equivalent to the last list element
having PC1297 or PC1309. It concludes exact equality with narrowTrace, or
widePrefix concatenated with the tail of wideEqualTail / wideLessTail. The shared
PC1283 state is included once. State counts 3/12/11 follow from classification;
there are respectively 2/11/10 transitions.

Successor lemmas derive registers from decoded instructions. A successful path
cannot pass PC1294's inconsistent assertion. No Step is defined after either
exit in this restricted block model. This means the block ends, not that the real
VM halts: production code exists beyond the modeled interval.

With one or three RangeCheck cells, selected by the final PC, `trace_to_execution`
constructs the earlier explicit-path witness. `trace_to_exitAssertions` and
`trace_to_conversionChecks` complete the numeric bridge. `trace_rt1_narrow`
additionally requires w<2^128 and equality of the block input to rt1FieldExpr.
Hints are not assumed correct. This proves neither production caller attribution
nor the existence of a real successful execution.

## Verification

75 named theorems (38 added), 36 boundary examples (16 added). Strict compilation,
scoped Lake build and the standard CLI's transitive axiom audit passed: 354 project
declarations, zero violations; propext, Classical.choice and Quot.sound only.
No sorryAx or native_decide; no claim of a minimal axiom set or independent audit.
The new examples check both Wide paths, RangeCheck cells, truncated traces,
self-loops, skipped control flow, forbidden steps after exits and impossible
length13. All earlier 20 examples are retained.

Three bounded Lean commands were used, including two compiler/linter failures.
The successful container peaked at 409948160 bytes (~391 MiB), under 8GiB RAM,
zero swap, one CPU and Lean -M6144. No OOM. Original Lake configuration restored;
exact execution configuration and all logs retained.

## Open obligations

Completeness is now closed **within the existing flat immutable-memory model**.
Correspondence to segmented Cairo VM memory/allocation and actual instructions,
production reachability and rt1 caller, compiler correctness, execution totality,
and whole-verifier/FIPS/quantum security remain open. JSON extraction is still
connected by recorded hashes and external checks, not a fully verified decoder.
The public integration exposes this model through the library and a bounded registry suite.

Historical local evidence (not included in this public export).
Historical local evidence (not included in this public export).
Historical local evidence (not included in this public export).

## Main theorems

- [execution_to_exitAssertions](../../Verification/MlDsaCasmBlockSemantics.lean#L394)
- [endsAtExit_iff_getLast](../../Verification/MlDsaCasmBlockSemantics.lean#L582)
- [no_exit_step](../../Verification/MlDsaCasmBlockSemantics.lean#L607)
- [no_trace_1294](../../Verification/MlDsaCasmBlockSemantics.lean#L620)
- [trace_classification](../../Verification/MlDsaCasmBlockSemantics.lean#L751)
- [trace_length_classification](../../Verification/MlDsaCasmBlockSemantics.lean#L765)
- [trace_to_execution](../../Verification/MlDsaCasmBlockSemantics.lean#L797)
- [trace_to_exitAssertions](../../Verification/MlDsaCasmBlockSemantics.lean#L812)
- [trace_to_conversionChecks](../../Verification/MlDsaCasmBlockSemantics.lean#L819)
- [trace_rt1_narrow](../../Verification/MlDsaCasmBlockSemantics.lean#L826)

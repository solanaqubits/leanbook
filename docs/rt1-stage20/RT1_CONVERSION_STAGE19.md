> Public rendering of a historical local report from `667f11d293347572f6dfa248dff88819ce26c430`.
> Raw execution logs are excluded; historical results below are not new public-tree verification.

# Stage 19: checked conversion paths for the rt1 arithmetic candidate

Status: **LOCALLY_VERIFIED_CANDIDATE_CONVERSION_PATHS**.
Base: `d2f7e6f6ff093ec2b02ad6b801862ebad6e91623`.
Module: [MlDsaRt1ConversionBlock.lean](../../Verification/MlDsaRt1ConversionBlock.lean).
SHA-256: `58ac1f4ab48d8282a1e798a824c3bb36d5e52a7f8838cc722b9a21d83ae77c1b`.

## Scope and correspondence

The new module pins 23 words at PC3641..3663 in Stage 15 production CASM
`4b817187ccc55e73f3837d5995e2dfb761217f898aa43359c323783cfa4e09e3`.
A fresh Python check compared every Lean literal with those production words.
All 14 fetch/decode cases and relative jump targets are checked by Lean decide.
The external JSON extraction/hash correspondence remains outside the Lean proof.

The module imports MlDsaCasmBlockSemantics and reuses its independent generic
DecodedStep rules. It defines a new fetch window, Step and CheckedTrace, with
new operands. It does not reuse the old 1274-address Step or assert that old
address-specific proofs apply unchanged. The six existing project modules remain
byte-identical; no bodies or theorem types were changed there.

New input=entryAP-4; selector=AP; shifted=AP+1; difference=AP+2; adjusted=AP+3;
high=AP+4; low=AP+5. The RC pointer is M[entryAP-24], with used cells at pointer+1
(Narrow) or pointer+1,+2,+3 (Wide). FP is unchanged by this modeled subset.

## Proved implication and explicit assumptions

`BlockExecution` consists of actual generic instruction-step checks along one
of three specified paths, numeric output bindings and separate RangeCheck bounds:

- Narrow:3641 ->3663 ->3664 (3 states).
- WideEqual:common prefix to3650, equality tail through3652/3654/3658/3659 ->6509
  (12 states including the shared prefix point once).
- WideLess:common prefix to3650, nonzero tail through3656/3658/3659 ->6509
  (11 states).

With canonical immutable flat memory, the new step-characterization lemmas derive
ExitAssertions, then reuse the already proved scalar assertion-to-ConversionChecks
implication. ExitAssertions/ConversionChecks are not execution premises. Correct
hints are not assumed: any admitted witness must satisfy the instruction equations
and RC conditions. Existence/termination of real executions is not proved.

Under the explicit premises w<2^128 and M[entryAP-4]=rt1FieldExpr w rt1Mask:

- `execution_rt1_narrow` returns the numeric tag narrow(packRotl64_1 w).
- `execution_rt1_option` returns the numeric Option view some(packRotl64_1 w).
- `rt1_no_wide_path` excludes either checked Wide path, including its 6509 endpoint.

`wide_paths_end_6509` records the external exit. fetch6509=none only means the
endpoint lies outside this local window, not that the VM halts or panics there.
The Wide tag is a numeric description of outgoing limbs, not a claim of successful
return by the enclosing Cairo function. The fail assertion at 3661 is impossible
in canonical memory.

## Verification and regressions

**48 named theorems, 26 examples.** Final `verify-02` passed scoped Lake --wfail,
strict compile and the standard CLI transitive audit: **461 project declarations**,
no violations, no sorryAx/native_decide, axioms propext/Classical.choice/Quot.sound.
The direct import and its closure are smaller than Stage 16e's memory-refinement
closure; the audit count is scoped to this module, not the entire project.
One fresh target in the 799-job Lake graph. No independent second auditor claimed.

Concrete complete memory witnesses exercise WideEqual(high=maxHigh,low=0),
WideLess(high=1,low=0), Narrow endpoints0 and2^128-1, new offsets/PCs and external
fetch boundaries. Negative examples reject wrong output, zero-high Wide,
high=maxHigh/low=1, invalid instruction addresses and the old jump immediate.
A trace with selector claiming Narrow and input2^128 passes equality-only steps
but fails RangeCheck: the examples explicitly demonstrate the necessity of RC.

First verify attempt:3.330s, only a strict comment line-length error. Corrected
without disabling linters. Final verifier:19.343s; peak 393592832 bytes (~375MiB),
Docker OOM=0. The bounded post-check revalidated source hashes and production words.
Original lakefile.toml restored after verification. No repeat audit was run on
unchanged final proof source.

## Boundaries, preservation and resources

This proves the three explicit finite paths. It does **not** reprove arbitrary
finite-trace completeness for the new window; Stage 16c's completeness applies to
its old fetch and cannot be transferred automatically. No new segmented-memory
refinement/witness lifting for this window is asserted.

Stage 18's arithmetic window PC3625..3635 is still a static candidate certificate;
its exact memory-to-input equation is an explicit premise here. Real Bitwise
segment membership, source-callsite/inline attribution, runtime/hints/deduction,
reachability, code after 6509 and full verifier/FIPS correctness remain open.

Separate 600s aggregate budget,120s/command,1CPU/8GiB/swap0/pids64,Lean-M6144,
minimum host MemAvailable 24GiB, no network/GPU/Cairo/USC/benchmarks. Resource totals
refer to bounded container payloads, not lightweight host orchestration.

[Final verifier — historical summary](rt1-stage20-public/historical-summary.json).
[Hash/word integrity — historical summary](rt1-stage20-public/historical-summary.json).
[Machine-readable status — historical summary](rt1-stage20-public/historical-summary.json).
[Knowledge card](../../knowledge/cryptography/MlDsaRt1ConversionBlock.en.md).

The local catalog now has 409 modules. No MasterSuite/root-import integration,
main/Quantum/SimLab modifications, git push or publication were performed.

Final bounded total: **23.607s / 600s**, including two Lean verifier attempts,
one integrity check and one knowledge-catalog check. All container runs had OOM=0.
The catalog/link check passed. The saved generate.py is a development scaffold;
input-01.lean and the final verified source record subsequent regression additions
and the linter correction, rather than claiming the scaffold regenerates the final file.

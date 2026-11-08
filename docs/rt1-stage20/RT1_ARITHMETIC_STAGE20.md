> Public rendering of a historical local report from `667f11d293347572f6dfa248dff88819ce26c430`.
> Raw execution logs are excluded; historical results below are not new public-tree verification.

# Stage 20: arithmetic slice to the candidate conversion input

Status: **LOCALLY_VERIFIED_ARITHMETIC_INPUT_BRIDGE**.
Base local commit: `efc8709b30f1c61c9cb9c23ba3facaf69be5aa42`.
Module: [MlDsaRt1ArithmeticBlock.lean](../../Verification/MlDsaRt1ArithmeticBlock.lean).
SHA-256: `d0eda5e7cbbd02046faa071d12b8cda5f6549fd981410190147bed39e74b8024`.

## Exact pinned scope

Production CASM SHA-256:
`4b817187ccc55e73f3837d5995e2dfb761217f898aa43359c323783cfa4e09e3`.
The new module contains the exact **16 words / 11 instructions at PC 3625–3640**.
A bounded Python integrity check compared all literals against the production JSON.
Lean checks all 11 fetch/decode results with `decide`. The external JSON parser and
artifact-to-literal extraction are not a verified Lean decoder.

Instructions PC 3625–3635 perform the arithmetic. PC 3636, 3638 and 3640 materialize
other values and advance AP three more times. They are included, rather than
assuming proximity implies value transfer. With initial AP=A and FP=F, the final
state is PC=3641, AP=A+9, FP=F; entryAP−4=A+5 exactly.

The module reuses the independent generic DecodedStep rules and defines its own
literal fetch window, Step and CheckedTrace. All seven previous modules, including
Stage 19, remain byte-identical. No old address-specific proof is automatically
transferred to this window.

## Proof chain and remaining premises

1. The first instruction constrains M[A] to M[F+25]*(1+2^64) modulo P.
2. Instruction assertions place M[A] and the exact mask in the Bitwise input cells
   B+5 and B+6, and read the output from B+7, where B=M[A−13].
3. The explicit relation `BitwiseAndAt M B` states only
   M[B+7] = M[B+5] AND M[B+6]. It contains no rt1 result or execution assertion.
4. Checked addition/multiplication/subtraction instructions give
   M[A+3]=(w+w)%P, M[A+4]=(t*D)%P and
   M[A+3]=(M[A+5]+M[A+4])%P. Canonical memory and modular cancellation derive
   M[A+5]=rt1FieldExpr w rt1Mask, including wrapped intermediate arithmetic.
5. AP accounting gives the Stage 19 input equation as a conclusion of
   `trace_to_rt1_input`, not as an assumption.
6. Under the additional source-lane bound M[F+25]<2^64, `trace_word` proves exact
   replication and w<2^128. Composing with a Stage 19 checked conversion path and
   its RangeCheck bounds yields narrow(packRotl64_1 w). Either checked Wide suffix
   to PC 6509 is impossible under these assumptions.

Memory is a completed immutable flat witness. The theorems do not assert that a
runner can compute every unknown cell in execution order. The input equality has
been discharged within this model; canonical memory, checked steps, the Bitwise
relation, source-lane bound and conversion RangeCheck obligations remain explicit.

## Checks, diagnostics and resources

**38 named theorems / 20 examples; 560 audited project declarations.**
The final verifier reports ok=true, source_unchanged=true, policy_findings=[],
no audit violations, no sorryAx and no native_decide. Allowed axioms:
propext, Classical.choice, Quot.sound. Scoped Lake --wfail, strict compilation and
CLI transitive audit passed. One new target was built in an 800-job graph.
This is a scoped check, not a fresh whole-library validation or independent audit.

Concrete complete-memory witnesses cover source inputs 0, 2^63 and 2^64−1. They
exercise canonical memory, the 11 arithmetic/bridge steps, the Bitwise relation,
Narrow conversion and RangeCheck. One end-to-end example invokes the composition
theorem at the high-bit wraparound input. Negative examples reject the old AP−1
input assumption, a changed result cell and a corrupted AND output. Further checks
cover the excluded source bound, instruction boundaries, length and address shift.

Diagnostics are preserved: verify-01 failed only two unused simp arguments;
verify-02 identified auxiliary regression proof syntax/API and Decidable issues.
These were corrected without disabling checks. verify-03 passed in **20.964s**,
peak **387055616 bytes (~369 MiB)**, Docker OOM=0. No unchanged final Lean source
was reverified. The temporary lakefile memory option was restored exactly.

Resource envelope: 1 CPU, 8 GiB, swap=0, pids=64, Lean -M6144; 120s/command,
600s aggregate; host reserve 24 GiB; no network, GPU, Cairo/USC compilations or
benchmarks. The run ledger counts bounded container payloads; host reads, edits,
git and coordination bookkeeping are outside that ledger.

## Open boundaries

- Real Bitwise builtin segment membership/alignment and its runtime semantics.
- Source-level static callsite and inline-instance attribution.
- Arbitrary-trace completeness for this new arithmetic/conversion window.
- Runtime reachability, segmented-memory refinement and hint/deduction execution.
- Semantics after PC 6509, compiler correctness, full verifier/FIPS/security claims.

Stage 19's numeric Wide tag and Option view keep their original model boundaries.
No behavior after the local exit is inferred. No main, Quantum, SimLab,
MasterSuite/root imports, publication or push changes were performed.

[Final verifier — historical summary](rt1-stage20-public/historical-summary.json).
[Word/hash integrity — historical summary](rt1-stage20-public/historical-summary.json).
[Structured status — historical summary](rt1-stage20-public/historical-summary.json).
[Knowledge card](../../knowledge/cryptography/MlDsaRt1ArithmeticBlock.en.md).

The saved generate.py is an initial development scaffold; input-01.lean and
input-02.lean preserve rejected versions. The final Lean source also includes
regression additions and diagnosed repairs; scaffold replay is not claimed.

Final bounded total: **32.281s / 600s** across three Lean
verifier attempts, one integrity check and one documentation check. OOM=0 in all
runs. The local knowledge catalog now contains 410 modules; all local links passed.

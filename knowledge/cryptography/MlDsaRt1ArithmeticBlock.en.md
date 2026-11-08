---
id: MlDsaRt1ArithmeticBlock
language: en
section: cryptography
source: Verification/MlDsaRt1ArithmeticBlock.lean
source_sha256: d0eda5e7cbbd02046faa071d12b8cda5f6549fd981410190147bed39e74b8024
proof_commit: 07ff174a798192995479d7a97928fb7ca2d25d55
novelty: not-assessed
status: locally-verified-arithmetic-input-bridge
---

# Candidate rt1 arithmetic and conversion input bridge

Stage 20 pins the 16 production words at PC 3625–3640 and applies the existing
`DecodedStep` semantics to their 11 instructions. The module imports
`Verification.MlDsaRt1ConversionBlock`; all seven preceding Lean modules are
unchanged. This is a local arithmetic/dataflow proof under an explicit Bitwise
relation, not source-callsite attribution or a proof about an external Cairo VM.

## Formal composed contract

Use the following distinct names:

- A and F: initial AP and FP at PC 3625.
- x = M[F+25]: the source lane, with the explicit precondition x < 2^64.
- w = M[A]: the packed word created by the first instruction.
- B = M[A−13]: the numeric address used for the local Bitwise buffer.
- entryAP = A+9: AP at the conversion entry PC 3641.

Under the hypotheses below, `trace_word` proves

\[
w = x(1+2^{64}) < 2^{128}.
\]

The composed result is

\[
\mathrm{out}=\mathrm{narrow}(\mathrm{packRotl64}_1(w)),
\qquad w=x(1+2^{64}).
\]

**The rotation argument is w, not the single source lane x.** Both packed halves
contain x. Omitting the factor (1+2^64) changes the asserted result.

The exact existing Lean contract is
`MlDsaRt1ArithmeticBlock.arithmetic_conversion_narrow`:

```lean
(hc : Canonical m)
(ht : CheckedTrace m (arithmeticTrace a f))
(hb : BitwiseAndAt m (m (a + -13) : Int))
(hx : m (f + 25) < 2 ^ 64)
(he : MlDsaRt1ConversionBlock.BlockExecution m (a + 9) f out)
⊢ out = .narrow (packRotl64_1 (m a))
```

This is a transcription of the checked theorem's hypotheses and conclusion,
not a newly compiled declaration. Numeric Option conversion additionally gives
`resultOption out = some (packRotl64_1 (m a))`; no downstream unwrap behavior is claimed.

| Remaining hypothesis | Exact model meaning |
| --- | --- |
| `Canonical m` | A completed immutable flat memory `Int → Nat`, with every cell < P. |
| `CheckedTrace ... arithmeticTrace` | All 11 decoded steps on the specified straight-line path hold; this is not a reachability theorem. |
| `BitwiseAndAt m B` | Only M[B+7] = M[B+5] AND M[B+6]. No runtime segment membership or alignment assertion is included. |
| `hx` | The original source lane M[F+25] is below 2^64. The provenance of this bound in the full caller is not established here. |
| `BlockExecution ... out` | One of the three Stage 19 paths, its instruction checks, separate RangeCheck bounds and numeric output binding. |

## Derived facts and discharged intermediate obligations

| Intermediate fact | How it is obtained |
| --- | --- |
| Bitwise inputs equal w and rt1Mask | Instructions at PC 3627, 3629 and 3630; the mask is a pinned literal. |
| t = w AND rt1Mask | `trace_and`, from the buffer equations and `BitwiseAndAt`. |
| Packed input fits 128 bits | `trace_word` derives exact replication and the bound from x < 2^64. |
| Result cell equals `rt1FieldExpr` | `trace_to_rt1_input`, using field addition/multiplication assertions and canonical modular subtraction. |
| Conversion input selects that result cell | All AP changes through PC 3640 are checked; (A+9)−4 = A+5. |
| `ExitAssertions` and `ConversionChecks` | Stage 19 derives them from the checked conversion path and RangeCheck bounds. |
| Narrow output; checked Wide suffixes impossible | Composition with the proved rt1 arithmetic and conversion theorems. |

The equation M[entryAP−4] = rt1FieldExpr w rt1Mask is a **derived conclusion**,
not an independent hypothesis of the composed theorem. No analogous claim removes
the explicit Bitwise relation or the checked-step premises. Modular wraparound
is allowed in intermediate field operations; the specific initial replication
is proved nonwrapping under the source-lane bound.

## Scope of the supporting modules

The current candidate uses the arithmetic window PC 3625–3640 and the conversion
window PC 3641–3663. Its proof chain reuses the scalar results in `MlDsaRt1`,
`MlDsaU128Conversion`, `MlDsaProductionConversionBlock`, and the generic decoded
instruction rules in `MlDsaCasmBlockSemantics`.

The older PC 1274–1296 window was attributed to transaction-version conversion in
Stage 17. Its arbitrary-trace classification, segmented-memory refinement in
`MlDsaCasmMemoryRefinement`, and compatible witness lifting in
`MlDsaCasmWitnessLifting` remain separate results. They are not automatically
transferred to the new addresses, operands or outgoing target.

## Open-obligation register

| ID | Open obligation | What the present result does establish |
| --- | --- | --- |
| RT1-O1 | Runtime Bitwise segment membership, alignment and semantics | A conditional consequence of the numeric AND relation. |
| RT1-O2 | Caller-level provenance of x < 2^64 | The bound implies exact replication and w < 2^128. |
| RT1-O3 | Classification of arbitrary traces in the new window | One specified arithmetic trace and three specified conversion paths are checked. |
| RT1-O4 | Segmented-memory refinement and correspondence to a pinned external VM | Soundness relative to the existing flat-memory decoded-step model. |
| RT1-O5 | Runtime deduction/initialization of hint cells and memory | Conditional checks on a completed immutable memory witness. |
| RT1-O6 | Source callsite and concrete inline-instance attribution | Matching arithmetic, pinned instructions and a checked local input bridge. |
| RT1-O7 | Reachability from a contract entrypoint | Conditional local path results; selected numeric witnesses do not prove runtime reachability. |
| RT1-O8 | Execution after PC 6509 | Both modeled Wide suffixes to that boundary are excluded under the contract; downstream code is not modeled. |
| RT1-O9 | Full compiler, verifier/FIPS and security correctness | The bounded arithmetic/conversion component only. |

## Main results

- [trace_and](../../Verification/MlDsaRt1ArithmeticBlock.lean#L192) identifies the
  AND cell from the explicit buffer relation and three instruction assertions.
- [trace_to_rt1_input](../../Verification/MlDsaRt1ArithmeticBlock.lean#L215) proves
  the conversion-input equation from the arithmetic trace.
- [arithmetic_conversion_narrow](../../Verification/MlDsaRt1ArithmeticBlock.lean#L240)
  composes with Stage 19: a checked conversion path with its RangeCheck conditions
  returns the numeric tag narrow(packRotl64_1 (M[A])).
- [arithmetic_no_wide](../../Verification/MlDsaRt1ArithmeticBlock.lean#L258)
  excludes both checked Wide suffixes ending at PC 6509 under the lane bound.
- `arithmetic_conversion_option` gives the corresponding numeric Option value;
  `trace_input_replicated` states the input equation in terms of M[F+25].

## Evidence and limits

38 named theorems and 20 examples. Kernel-checked fetch facts cover all 11
instructions. Concrete completed memories exercise inputs 0, 2^63 and 2^64−1,
the arithmetic trace, Narrow conversion steps and RangeCheck. Negative examples
reject an incorrect AP−1 input, a corrupted result cell and a wrong AND slot.

Strict compilation, scoped Lake build and the standard CLI import-closure audit
passed: 560 project declarations, no violations, no sorryAx/native_decide; allowed
axioms propext, Classical.choice and Quot.sound. Only this module was freshly
built in the 800-job graph; this is not a new full-library validation.

The explicit straight-line trace and three specified conversion paths are checked.
Completeness for arbitrary traces, actual runtime execution and deduction of hint
cells, Bitwise pointer provenance, source/inline attribution, reachability,
segmented-memory refinement for this window and code after PC 6509 remain open.
The source lane bound remains an explicit precondition. Existence of selected
completed numeric witnesses does not establish a real runtime execution.

[Stage 20 report](../../docs/rt1-stage20/RT1_ARITHMETIC_STAGE20.md).
[Historical summary](../../docs/rt1-stage20/rt1-stage20-public/historical-summary.json).
[Historical summary](../../docs/rt1-stage20/rt1-stage20-public/historical-summary.json).

[Consolidated local verification checkpoint](../../docs/rt1-stage20/RT1_VERIFICATION_CHECKPOINT_STAGE20.md).

## Public synchronization

The preceding validation counts describe the local research checkpoint.
[New public-tree checks and exclusions](../../docs/rt1-stage20-public.md) are recorded separately.

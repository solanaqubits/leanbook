> Public rendering of a historical local report from `667f11d293347572f6dfa248dff88819ce26c430`.
> Raw execution logs are excluded; historical results below are not new public-tree verification.

# rt1 verification checkpoint: local results through Stage 20

Report status: **DOCUMENTED_LOCAL_VERIFICATION_CHECKPOINT**.
Proof status: **LOCALLY_VERIFIED_ARITHMETIC_INPUT_BRIDGE**.
This closes the report for the current local checkpoint, not the full Cairo–Lean
verification obligation. No new theorem or runtime certification is introduced.

## Pinned evidence

| Item | Identity |
| --- | --- |
| Production CASM Stage 15 | SHA-256 `4b817187ccc55e73f3837d5995e2dfb761217f898aa43359c323783cfa4e09e3`, 81,499 felts |
| Arithmetic and AP bridge | PC 3625–3640: 16 words, 11 instructions |
| Candidate conversion | PC 3641–3663: 23 words, 14 instructions |
| Stage 19 proof commit | `efc8709b30f1c61c9cb9c23ba3facaf69be5aa42` |
| Stage 20 proof commit | `07ff174a798192995479d7a97928fb7ca2d25d55` |
| Contract documentation commit | `82866c36b8c8f6b770f7dc9011fc12b556c54bde` |
| Stage 20 Lean source | SHA-256 `d0eda5e7cbbd02046faa071d12b8cda5f6549fd981410190147bed39e74b8024` |

Production JSON identity and extraction were checked externally. Literal decoding
and the stated deductions were checked in Lean. This does not turn the external
JSON parser into a verified decoder or establish source-level callsite attribution.

## Exact composed contract

Let A and F be the initial AP and FP, x = M[F+25], B = M[A−13], and w = M[A].
The proof requires all five groups of hypotheses:

1. Canonical completed immutable memory M : Int → Nat, with every cell below P.
2. Checked steps of the specified arithmetic trace PC 3625 through entry PC 3641.
3. The explicit numeric relation M[B+7] = M[B+5] AND M[B+6].
4. The source-lane bound x < 2^64.
5. A Stage 19 `BlockExecution` at AP=A+9: a checked specified conversion path,
   its RangeCheck bounds, and the numeric output binding.

Together these give

\[
w=x(1+2^{64})<2^{128},\qquad
\mathrm{out}=\mathrm{narrow}(\mathrm{packRotl64}_1(w)).
\]

The argument of packRotl64_1 is the replicated 128-bit word w, not x alone.
Canonical memory and RangeCheck by themselves are not the complete contract.

The arithmetic and bridge instructions derive

\[
\mathrm{entryAP}=A+9,\qquad
M[\mathrm{entryAP}-4]=M[A+5]
 =\mathrm{rt1FieldExpr}(w,\mathrm{rt1Mask}).
\]

Thus the conversion-input equality is discharged as an independent premise.
Bitwise semantics and the checked-step premises are not discharged by this fact.
The composed theorem gives the numeric Option view `some(packRotl64_1 w)` and
excludes both checked Wide suffixes ending at PC 6509. It does not execute code
at that external address or prove real unwrap/panic behavior.

Exact theorem types and source links are in the
[contract card](../../knowledge/cryptography/MlDsaRt1ArithmeticBlock.en.md).

## Supporting results and address boundaries

| Module | Role at this checkpoint |
| --- | --- |
| `MlDsaRt1` | General arithmetic rotation correspondence for the exact mask and bounded packed word. |
| `MlDsaU128Conversion` | Numeric Narrow/Wide constraints, canonicality and uniqueness of Narrow for bounded input. |
| `MlDsaProductionConversionBlock` | Scalar assertion-to-conversion bridge; pinned old PC 1274–1296 words. |
| `MlDsaCasmBlockSemantics` | Generic decoded-step semantics reused by the new modules; old-window path soundness and completeness stay address-specific. |
| `MlDsaRt1ConversionBlock` | New PC 3641–3663 finite-path soundness with new offsets and external target. |
| `MlDsaRt1ArithmeticBlock` | New arithmetic input derivation and composition with the conversion contract. |
| `MlDsaCasmMemoryRefinement` | Separate forward refinement for the old block in an abstract segmented model. |
| `MlDsaCasmWitnessLifting` | Separate compatible-witness lifting for the old three paths; no arbitrary reverse simulation. |

Stage 17 attributed the old PC 1274–1296 block to transaction-version conversion,
not rt1. That finding does not invalidate its conditional numeric theorems. Its
trace completeness and memory results do not automatically transfer to the new
window. Stage 18's proposed `k2::lad` source location remains a structural hypothesis.

## Verification receipts

| Scope | Named theorems / examples | Audited closure | Final successful bounded verifier run |
| --- | --- | --- | --- |
| Stage 19 | 48 / 26 | 461 declarations | 19.343 s; 393,592,832 bytes peak (~375 MiB) |
| Stage 20 | 38 / 20 | 560 declarations | 20.964 s; 387,055,616 bytes peak (~369 MiB) |

Both receipts include strict compile, scoped Lake build and the standard CLI
transitive audit, with zero violations, no sorryAx and no native_decide. Allowed
axioms were propext, Classical.choice and Quot.sound. Closure counts overlap and
must not be added or presented as independent proof counts. These are scoped
receipts, not a fresh full-library audit or an independent second audit.

Stage 20 preserved its failed development attempts and successful final run.
Its bounded payload total was 32.281 s; the final verifier time is only one part
of that total. All recorded Stage 20 container runs had OOM=0. Final-source proofs
were not rerun for this documentation checkpoint.

- [Stage 19 report](RT1_CONVERSION_STAGE19.md) and [verifier receipt — historical summary](rt1-stage20-public/historical-summary.json).
- [Stage 20 report](RT1_ARITHMETIC_STAGE20.md) and [verifier receipt — historical summary](rt1-stage20-public/historical-summary.json).
- [Stage 20 literal/source integrity — historical summary](rt1-stage20-public/historical-summary.json).

## Open obligations

The identifiers below preserve the contract card's register. Compiler, full
verifier/FIPS and security obligations remain separate components of RT1-O9;
listing them separately must not drop source-bound or hint-deduction obligations.

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

## Repository and documentation scope

All eight Lean modules remain unchanged at this checkpoint. The knowledge catalog
still contains 410 modules. This update adds the summary and navigation links;
it does not change proof status, run Lean, publish, push or integrate main,
Quantum, SimLab or MasterSuite. Historical Stage 19/20 receipts remain unchanged.

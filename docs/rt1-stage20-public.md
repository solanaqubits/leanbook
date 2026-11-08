# Public rt1 synchronization through Stage 20

Source: `667f11d293347572f6dfa248dff88819ce26c430`.
Public base: `38897a3ddaac9c8e95b21db452533ed4c8b5fb83`.
Four of eight source modules already matched main exactly. This export adds only
MlDsaCasmMemoryRefinement, MlDsaCasmWitnessLifting, MlDsaRt1ConversionBlock and
MlDsaRt1ArithmeticBlock, their cards, catalog/navigation and a registry field
packaging the existing composed theorem. All eight mathematical files remain
byte-identical to the local checkpoint. Existing registry fields are retained.
The standard integration recipe reports no root/parent changes needed.

## Contract and open boundaries

Let x=M[F+25], w=M[A]=x*(1+2^64). Canonical completed immutable flat memory,
the specified arithmetic steps, the explicit numeric BitwiseAndAt relation,
x<2^64 and a checked conversion path with RangeCheck and output binding imply
out=narrow(packRotl64_1(w)). The trace derives entryAP=A+9 and
M[entryAP-4]=M[A+5]=rt1FieldExpr(w,rt1Mask); this equality is not a separate premise.
BitwiseAndAt states only M[B+7]=M[B+5] AND M[B+6], not builtin segment membership,
alignment or runtime correctness.

The old PC1274–1296 block was attributed to tx_version in Stage17. Its completeness,
segmented-memory refinement and witness lifting are not transferred to the new
PC3625–3640 arithmetic and PC3641–3663 conversion windows.

The [contract card](../knowledge/cryptography/MlDsaRt1ArithmeticBlock.en.md) preserves
RT1-O1–O9: runtime Bitwise; provenance of x<2^64; arbitrary new-window traces;
segmented memory/external VM; hint-cell initialization; source/inline attribution;
reachability; execution after PC6509; compiler, full verifier/FIPS and security.

## Evidence and exclusions

[Historical checkpoint rendering](rt1-stage20/RT1_VERIFICATION_CHECKPOINT_STAGE20.md),
[Stage19](rt1-stage20/RT1_CONVERSION_STAGE19.md), and
[Stage20](rt1-stage20/RT1_ARITHMETIC_STAGE20.md) retain their local-checkpoint claims.
[Derived historical summaries](rt1-stage20/rt1-stage20-public/historical-summary.json)
record original receipt hashes and selected verdict fields. They are explicitly
not byte-identical original receipts or new checks. The original archives remain
untouched. Public renderings repair links to excluded execution logs.

Private SimLab material, raw command/configuration logs with host paths, Docker
inspect, host-meminfo, coordination registries, failed/scaffold drafts and production
binaries are excluded. No new Cairo compilation, benchmark or mathematical
research is performed. Quantum sources and private SimLab are untouched.

New bounded public-tree verification is recorded separately in
[new evidence](rt1-stage20/rt1-stage20-public/verification.json). Shared Mathlib is
read-only; the execution-only -M6144 limit does not change the published Lake
configuration. This is a delta batch integration, not a new beta or release tag.
Hosted CI on the exact published SHA is reported separately; pending is not success.

## New local result

Strict Cairo verification audited 1,088 project declarations; the registry audit
covered 45,617, and the planner-selected AxiomAudit root covered 45620. All passed
with unchanged sources, no policy findings, and only propext, Classical.choice
and Quot.sound. These overlapping counts are not summed. All 34 selected tests
passed without skips. The affected consumer build used the existing cache.
No OOM or resource-limit failure occurred; bounded payload time was 156.371 seconds.

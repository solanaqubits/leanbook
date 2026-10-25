# Source-informed optimization work package

Status: isolated pilot, prepared for a combined audit; not a release qualification.
Parent: corrective candidate `444e9e4ba37db6e0cd2f7c828dca02248051636f`.
The failed published v0.9.0 checkpoint remains a separate audit subject.

## Pinned observations and transfer decisions

These are source inspections on 2026-10-25, not independent upstream builds,
security audits, leaderboard checks or reproduction of reported scores.

| Source | Observed technique | Our bounded transfer | Remaining obligation |
| --- | --- | --- | --- |
| [MODEXP README, 28e628b4](https://github.com/Layr-Labs/eip8200-challenges/blob/28e628b4f55204460d7cd815f1715c10921b9785/Challenge/Modexp/Submission/README.md) | Records modular-word rewrites, preserved byte offsets, and a zero/nonzero observation contract for branch conditions. Separates matched local gas measurements from hosted scores. | Future local word-rewrite library: explicit width, stack/frame, observable output and artifact mapping. | A word identity alone is not EVM block equivalence; gas and bytecode binding need separate proofs. |
| [labinius comparison, 6de95237](https://github.com/Layr-Labs/labinius-fast-challenge/blob/6de95237b03b90ed360b13099587d6846410a979/solution/native_diagnostics/src/compare.rs) | Full-output comparison, two warmups, eight samples, varied order, timers stopped before checking/logging. | Original two-variant ALCC diagnostic with an independent exact reference and a generated-C timing-order check. | Local timings do not certify whole-checker throughput or hardware-independent improvement. |
| [Proximity Solution, aec85b65](https://github.com/proximity-prize/proximity-prize/blob/aec85b65a60d68bc84cc1ee2baa5fd75b613586a/ProximityPrize/SubmissionBinaryUpper/Solution.lean) | `score_nat` uses kernel `decide`; subsequent lemmas transport a natural-number inequality to the stated real-power score. | Future exact-bound module: rational candidate, positive denominators, integer certificate, order-preserving transport. | No inference from ALCC identity acceptance to inequality validity; no unreviewed floating-point rounding. |
| [sig.golf packaging, b4a7c9f](https://github.com/Layr-Labs/sig.golf/blob/b4a7c9f16149018bc9e52a176415faa0f206b5aa/submission/SigGolfCandidate/Packaging_Ready.lean) | Assembles refinement, termination, admissibility, cycle and security dependencies into a certificate indexed by 7008. | Future explicit ALCC obligation bundle separating semantics, implementation, artifacts and cost. | Names such as `paired_expand_pending` are not evidence of either missing or completed proofs; inspect dependency types and audit transitively. |

No external source code is copied into this package and no external dependency is
added. Attribution is retained through immutable source links. MODEXP's README
claims inherited Apache notices; Proximity's inspected file has an Apache header.
This is not a license clearance of their entire dependency trees. The inspected
labinius and packaging files do not establish a repository-wide license grant.
Any later file reuse requires checking its actual license and retained notices.

## First implemented pilot: cache coefficients

The production ALCC normalizer computes each surviving coefficient during both
filtering and output construction. The candidate maps distinct exponent vectors
to coefficient records once, filters those records, then sorts by the exponent.
It retains the existing coefficient calculation and insertion-sort strategy.

[AlgebraicCertificateNormalizeCached](../Verification/AlgebraicCertificateNormalizeCached.lean)
proves exact equality to `normalize` for every dimension and every rational sparse
list, including repeated vectors, zero terms and cancellation. Denotation and
checker-result preservation follow. The production `normalize`, `checkCert`,
byte decoder and CLI remain unchanged. This pilot is not added to MasterSuite;
no new direct-import count or module ordinal is claimed.

The experimental `alcc-normalize-bench` target uses three-dimensional inputs for
measurements only. The theorem is not restricted to that measurement corpus.
The SimLab companion contains the exact reference, bounded corpus, protocol tests
and comparison driver. See its `docs/alcc-normalization-pilot.en.md` contract.
The first runtime pilot is blocked at initialization under its fixed 1-GiB
address-space cap, before any normalization result. There are no accepted timing
samples or demonstrated performance gains. The semantic refinement proof is
independent of that infrastructure failure.

## Combined audit acceptance checklist

1. Keep published `ef78e9d`, corrective `444e9e4`, and this pilot distinct. Reconcile
   exact commits before integrating; do not reuse old release qualification.
2. Review the cached-list equality proof and its dependency axioms. Verify that
   the production checker is unchanged and the benchmark calls the proved code.
3. Inspect generated code: clock, non-inlined computation, clock, serialization.
   A pure expression between clocks can be moved past the second clock.
4. Recompute the frozen corpus using the independent rational accumulator; reject
   any difference in the full output, including validation and warmup rounds.
5. Review sample order, excluded work, limits, clock resolution and raw timings.
   Preserve slowdowns and failures; do not select only favorable cases.
6. Audit the verifier correction and all 13 earlier modules separately. Run a
   new full beta on the final combined bytes before a new public checkpoint.
7. Keep the other three transfer directions as open tasks until their own
   implementations, meaningful tests and proof/implementation links exist.

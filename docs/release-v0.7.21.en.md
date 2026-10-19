# v0.7.21 — Hidden scalar fork progress probability

This scoped release exports epsilon216,
`Verification.CryptoHiddenScalarForkProgressProbabilityContract`, from snapshot
`5b58cc9959eb47a6d1b99d03f062b3084852e214`.
There are 216 direct MasterSuite imports and 260 formal Lean sources, including
Verification.lean. All 260 match the pinned source snapshot byte for byte.

## Result and exact premises

`retainedCount` follows prefixes of the existing epsilon215 collector. It starts
at zero, stays below quota n and increases by zero or one on each probe. Only
retained successful keys block insertion. Failed calls can be retried with new
child schedules. `KeyCoherent` connects candidate labels to returned keys;
without it, reaching list length n need not pass final distinct-key selection.

For a nonempty finite uniform seed set and schedules of length T, `ProgressBounds`
requires explicit lower bounds p(j) in [0,1] on the next progress mass conditional
on current time and retained count j. No independence or Markov assumption about
the actual process is used. `quota_probability_lower` proves that the absorbing
reference recurrence H(T,0) lower-bounds actual quota attainment:
H(0,j)=1[j>=n], H(b+1,j)=1 for j>=n; otherwise
H(b+1,j)=(1-p(j))*H(b,j)+p(j)*H(b,j+1).

`collect_probability_lower` applies the bound to the actual collector, including
non-clean successful schedules. Exact event adapters cover quotas 4 (distinct
nonzero squares), 2 (unit eta calls) and 3 (outer calls) at concrete reachable
snapshots. `positive_progress_extracts` composes positive success probability
with model-relative provenance and the existing witness-or-relation extractor.
`unblocked_probability_lower` controls the mass lost by excluding retained classes
within the same conditional finite experiment. Child success density remains a
premise; it is not inferred from a global acceptance probability.

T counts local candidate probes, not primitive queries or physical time.
Epsilon215 schedule bounds and ResourceTrace remain applicable. Exact
Q(k)=4+2(4^(k+1)-1), R(k)=Q(k)-1 are restricted to Clean successful runs;
InitialAdversaryAbort has Q=1,R=0.

## Validation and limits

Public epsilon/scoped verification runs strict Lake build, 44 selected live tests,
one union transitive declaration audit with strict AxiomAudit, and metadata,
knowledge and whitespace checks. Allowed axioms: propext, Classical.choice,
Quot.sound. Public evidence is generated independently of private receipts.
Incremental build artifacts are retained.

New coverage: 33 Lean examples, 3 helper theorems and 21 executable scenarios.
Cases include success mass 1/2 versus clean mass 1/4, correlated repeats invalidating
a marginal-only estimate, inconsistent keys, budget/rate boundaries, blocked
classes and depth-one F11 acquisition after failure with extraction.

Lake remains 0.7.1. The full public beta basis remains
`2419489245019fb16e32ffac641b9f88eea94126`; no new full beta or remote CI run is claimed.
Global acceptance-to-local progress, general Bellare–Neven bounds, external-process
refinement, Fiat–Shamir/ROM and polynomial-time guarantees remain open.
Novelty is not-assessed. Only allowlisted Lean sources, integration metadata,
regressions and English documentation are exported.

---
id: CryptoHiddenScalarQuotaComparisonContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaComparisonContract.lean
novelty: not-assessed
status: reviewed
---

# Structural comparison of tabular and streaming quota search

Epsilon232 adds TabularStats (checks, inits, transitions, updates).
quotaRowInstrumented accumulates one initialization and T transitions, using the
actual update annotations from quotaNextRowCounted. Its row equals quotaRow and
its counters equal (0,1,T,n*T). quotaProbeInstrumented preserves the original
j<n guard before constructing a row. chooseQuotaBudgetTabularInstrumented mirrors
searchThrough control; after a successful prefix it runs no additional probes.
Its Option projection equals chooseQuotaBudgetTabularWithin for every rational
profile, tolerance and cap, with no probability-range assumptions.

Let t be the selected budget on some, or cap on none. For j<n the exact stats
are (t+1,t+1,triangular t,n*triangular t). The recursive sum first satisfies
2*triangular t=t*(t+1), then triangular t=t*(t+1)/2 in natural arithmetic.
Counters accumulate during evaluation; closed forms are proved, not assigned.

streamingStats extends the existing SearchStats with the one initial row present
in the root definition, preserving every existing counter and API. Its stats are
(t+1,1,t,n*t). nonabsorbed_comparison, nonabsorbed_savings and nonabsorbed_strict
establish equal checks and savings only for j<n. Savings are t initializations,
t*(t-1)/2 transitions and n*(t*(t-1)/2) active updates. Strict initialization
savings hold iff t>=1; transitions iff t>=2; updates iff t>=2 and n>0.
Here j<n already implies n>0.

For j>=n the tabular probe constructs no rows: inits/transitions/updates=0.
Nonnegative tolerance gives some0 with one check; negative tolerance gives none
with cap+1 checks. The streaming model still initializes a row and, for negative
tolerance, performs cap transitions and n*cap active updates. absorbed_comparison
and regressions explicitly refute a universal streaming advantage. One predicate
check does not imply constant total execution: searchThrough descends from cap.

The model excludes recursive search control, stack cost, profile evaluation,
rational bit arithmetic, instrumentation overhead, compiler optimizations,
allocations, memory and wall-clock time. No library IsBigO theorem or new
benchmark is claimed. Previous timings do not prove causal attribution of speedup;
reference and tabular are different selectors. Novelty remains not-assessed.

30 IO scenarios run inside a compound live test; 36 Lean examples include registry
projections. Cases cover both state regimes, zero quota/cap, negative tolerances,
nonprobabilistic profiles, some/none, calibrations4/6, equality at t=1 and strict
savings at t>=2. Epsilon/scoped checks; full beta baselines retained.

[Lean](../../Verification/CryptoHiddenScalarQuotaComparisonContract.lean)

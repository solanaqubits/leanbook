---
id: CryptoHiddenScalarQuotaCostContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaCostContract.lean
novelty: not-assessed
status: reviewed
---

# Structural accounting for streaming quota search

The counted transition annotates each active entry (i<n) by one update and the
absorbing entry by zero. Removing annotations yields exactly quotaNextRow for
any input row; their sum is n. SearchStats records checks, transitions and updates.
The counted scan checks the current row even at zero fuel; only a failed check
with remaining fuel invokes the counted transition and accumulates its updates.
Counters are accumulated along recursion, not defined from the final answer.

Projection equals both the streaming and reference selectors for all rational
profiles, tolerances and caps, with no probability-range assumptions. At arbitrary
start T and row, quotaInstrumentedScan_stats proves checks=transitions+1,
updates=n*transitions, transitions<=fuel, and either k=T+transitions on some k
or transitions=fuel on none. Starting at zero, exact stats are (k+1,k,n*k) on
success and (cap+1,cap,n*cap) on failure. The three counters have cap bounds.

structuralCost = checks + (n+1)*(transitions+1) counts one unit per budget check
and per entry of the initial and subsequent materialized rows, including the
absorbing entry. structuralCost_bound proves <= 2*(n+1)*(cap+1), including n=0
and cap=0. This is an explicit natural-number unit-cost inequality, not a theorem
using a library Big-O predicate.

An active source expression contains two occurrences of p i, one subtraction,
two multiplications and one addition, with no explicit division. Profile evaluation,
rational bit costs, comparisons and instrumentation overhead are not bounded.
The counters do not describe compiled instructions, allocations, live memory or
wall-clock time. Prior finite benchmarks remain separate empirical evidence.

26 IO scenarios run inside one compound live test; 32 kernel examples include
registry projections. Cases cover early success, exhaustion, zero quota/cap,
absorption with negative tolerance, heterogeneous/non-probabilistic profiles,
calibrations 4/6 and a nonzero starting budget. Epsilon/scoped verification;
full beta baselines retained, no public release in this stage. Novelty not-assessed.

[Lean](../../Verification/CryptoHiddenScalarQuotaCostContract.lean)

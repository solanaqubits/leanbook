# v0.7.39 — exact structural costs of quota resumption

Adds CryptoHiddenScalarQuotaResumeCostContract (epsilon235), registry integration,
compact regressions and English documentation. Pinned private source:
`0a5ece6c6a518c7b3659b6785bf346316e7b6e67`. Inventory: 237 direct MasterSuite
imports and 281 byte-identical Lean sources including Verification.lean.

Instrumented start and continuation preserve the full QuotaSearchResult,
including the exhausted cursor bound and actual retained vector row.
Counters follow actual branches and quotaNextRowCounted transitions rather
than being computed afterwards from the returned budget.

The four TabularStats fields are checks, inits, transitions and updates.
A start stopping at t has counts (t+1,1,t,n*t). Continuation from exhausted
bound b to a newly reached budget t has counts (t-b,0,t-b,n*(t-b)).
Covered windows and terminal found results add zero in all four counters.
Under cap1<=cap2, the sum of start(cap1) and resume(cap2) counters equals
cold streamingStats(cap2), the epsilon232 adapter adding one initialization
to the epsilon231 counters. All rational profiles and tolerances are allowed.
Full equality with the original resumable algorithm is unconditional;
its equivalence to a cold search retains the earlier minimality/cap premises.

30 IO scenarios run inside the compound live test; 38 Lean examples include
registry checks. Shrinking-window counterexamples cover success and exhaustion.
Guards, data packaging, stack, instructions, physical allocation and rational
bit costs are outside the structural model. No benchmark or serialization claim.

Independent public epsilon/scoped validation uses strict Lake, all public
unittests with live mode, integration/catalog checks and a single transitive
union axiom audit. Allowed axioms: propext, Classical.choice, Quot.sound;
no native_decide. Explicit qutrit Spec building and the old memory fix remain.
Local checks preserve the incremental cache under an 8 GiB memory cap with
swap off. Lake remains 0.7.1. The full public beta remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1); no new full beta checkpoint.
Private coordination, research files, raw evidence and ancestry are excluded.

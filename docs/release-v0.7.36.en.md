# v0.7.36 — exact tabular and streaming quota cost comparison

Adds CryptoHiddenScalarQuotaComparisonContract (epsilon232), registry integration,
compact regressions and English documentation. Pinned private source:
`cf3551f1953dd98900004f9084e93faaf70bc2d4`. Inventory: 234 direct MasterSuite
imports and 278 byte-identical Lean sources including Verification.lean.

Instrumented tabular search preserves the original Option result for arbitrary
rational profiles, tolerances and search caps, without probability restrictions.
For j<n and t equal to the successful budget (or cap on exhaustion), tabular
checks and initializations equal t+1; transitions equal t*(t+1)/2 and active
updates equal n*t*(t+1)/2. Streaming uses the same checks, one initialization,
t transitions and n*t updates. Exact transition savings are t*(t-1)/2;
strict savings require t>=2 (and n>0 for active updates).

The absorption guard is preserved: at j>=n the tabular selector builds no rows.
Streaming still initializes a row and, for negative tolerance, performs cap
transitions. No universal streaming superiority is claimed.
This is a source-level structural model, excluding search-control overhead,
rational bit costs, profile evaluation, compiled instructions, allocations,
algorithm memory and machine time. No separate IsBigO theorem is asserted.
30 IO scenarios run within the compound live test; 36 Lean examples include
registry checks. Explicit qutrit Spec building and the old memory fix are preserved.

Independent public epsilon/scoped validation uses strict Lake, all public
unittests with live mode, integration/catalog checks and a single transitive
union axiom audit. Allowed axioms: propext, Classical.choice, Quot.sound;
no native_decide. Local checks preserve the incremental cache under an 8 GiB
memory cap with swap off. Lake remains 0.7.1. The full public beta remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1); no new full beta checkpoint.
Private coordination, research files, raw evidence and ancestry are excluded.

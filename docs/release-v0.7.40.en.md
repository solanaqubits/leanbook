# v0.7.40 — full state and cost equality of quota chains

Adds CryptoHiddenScalarQuotaChainContract (epsilon236), registry integration,
compact regressions and English documentation. Pinned private source:
`cb3161bb5958bb2e3db5e4c4bc57df9300b00e6f`. Inventory: 238 direct MasterSuite
imports and 282 byte-identical Lean sources including Verification.lean.

cursor_ext identifies valid cursors with equal bounds via row_correct and proof
irrelevance. The full-result bridge resume(start(a),b)=start(b) requires a<=b.
An executable left-to-right fold calls instrumented continuation and adds its
actual four counters. One induction proves equality of the entire result/cost
pair with a cold start at lastCap under List.IsChain (<=) (cap0::caps).
This identifies the exact retained bound and vector on exhaustion.
The same nondecreasing-chain premise applies to the toOption equality with
chooseQuotaBudgetWithin. Arbitrary rational profiles and tolerances are allowed.
An empty tail means one start at cap0; repeated caps are allowed.

With t equal to the selected budget or lastCap on refusal, total fields
(checks,inits,transitions,updates) are (t+1,1,t,n*t). streamingStats is the
epsilon232 adapter adding one initialization to epsilon231 counters.
32 IO scenarios run inside the compound live test; 40 Lean examples include
registry checks. Cases include calibrations4/6, exact exhausted rows,
empty/repeated chains, negative tolerances, outside-range profiles and absorption.
Shrinking after success and exhaustion refutes universal equality without
monotonicity; not every nonmonotone chain is asserted to violate equality.
Guards, packaging, stack, physical allocation and rational bit costs are excluded.
No benchmark, serialization or external cursor authentication is claimed.

Independent public epsilon/scoped checks include strict Lake, all public
unittests with live mode, catalog/integration checks and one transitive union
axiom audit: only propext, Classical.choice, Quot.sound; no native_decide.
Explicit qutrit Spec building and the old memory fix are preserved.
Local checks retain incremental caches under an 8 GiB cap with swap off.
Lake remains 0.7.1; full public beta remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1), not a new beta checkpoint.
Private coordination, research material, raw evidence and ancestry are excluded.

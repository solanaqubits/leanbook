# v0.7.41: Fast successful starts of resumable quota search

This scoped release exports epsilon237, CryptoHiddenScalarQuotaFastStartContract.
The public tree contains 239 direct MasterSuite imports and 283 Lean sources,
byte-identical to the pinned private formal sources.

`startQuotaSearchFast` preserves the full `QuotaSearchResult` of the existing
start for every rational profile, tolerance and cap. Exhausted cursor bounds
and rows are unchanged. Absorbed states with nonnegative tolerance and
unabsorbed states with tolerance at least one return `found 0` directly.

The instrumented success has `(checks,inits,transitions,updates)=(1,0,0,0)`.
Delegation adds one failed outer threshold check to the old start, giving
`(t+2,1,t,n*t)`, where t is the selected budget or the exhausted cap.
Negative tolerances are not globally rejected for arbitrary rational profiles.

24 IO scenarios and 33 Lean examples including registry cover zero and positive
caps, absorption, arbitrary profiles, calibrations 4/6 and exact retained rows.
The explicit qutrit Spec build remains in place.

These are structural counts, excluding natural guards, packaging, runtime,
physical allocations and rational bit complexity. Chain-cost extensions and
new performance measurements are not part of this release.

Lake remains 0.7.1. Full public beta basis
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1) is unchanged;
independent scoped checks do not create a new full beta checkpoint.

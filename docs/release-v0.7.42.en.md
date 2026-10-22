# v0.7.42: Resume chains with one fast start

This scoped release exports epsilon238, CryptoHiddenScalarQuotaFastChainContract.
The public tree contains 240 direct MasterSuite imports and 284 Lean sources,
byte-identical to the pinned private formal sources.

The executable fold starts from startQuotaSearchFastInstrumented and calls the
existing instrumented continuation on each cap. Under
`List.IsChain (<=) (cap0::caps)`, its full state/cost pair equals a single cold
fast start at lastCap, including the exhausted cursor bound and row.
Its toOption equals the reference selector under the same chain premise.
Arbitrary rational profiles and tolerances are allowed.

Fast success has `(checks,inits,transitions,updates)=(1,0,0,0)`.
Fallback has `(t+2,1,t,n*t)`, where t is the selected budget or lastCap on
exhaustion: exactly one additional threshold check for the entire chain.
Fast success and the one-check offset versus the old executed chain hold for
any tail; equality with a cold final-cap search requires nondecreasing caps.

30 IO scenarios and 41 Lean examples including registry cover empty/repeated
bounds, initial/intermediate success, exhaustion with exact rows, absorption,
calibrations 4/6, arbitrary profiles, negative tolerances and shrinking
counterexamples. The explicit qutrit Spec build remains in place.

Structural counts exclude natural control guards, packaging, stack, physical
allocations and rational bit complexity. No performance measurement or cursor
serialization is included.

Lake remains 0.7.1. Full public beta basis
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1) is unchanged;
independent scoped checks do not create a new full beta checkpoint.

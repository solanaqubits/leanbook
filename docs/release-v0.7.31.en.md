# v0.7.31 — Constructive quota budgets

This epsilon/scoped release exports epsilon227,
`Verification.CryptoHiddenScalarQuotaBudgetContract.lean`, from pinned source
`90c304d73f6603e68c142b2f9c10196b23428b21`. It contains 229 direct MasterSuite
imports and 273 byte-identical formal Lean sources including Verification.lean.
Only the reviewed module, integration, tests and English documentation are exported.
Private history, coordination, research archives and knowledge graphs are excluded.
Apache-2.0 licensing is retained.

## Contract

chooseBlockCount P epsilon returns the least K satisfying (1-P)^K<=epsilon.
For 0<P<1 and 0<epsilon<1 its finite rational search uses the cap
ceil((1-epsilon)/(P*epsilon)), justified by (1-P)^K<=1/(1+K*P).
Soundness, strict minimality, existence and positivity are proved. Endpoint and
invalid cases are explicit: tolerance>=1 selects0 on admissible P; P=1 with
0<=epsilon<1 selects1; P=0 below tolerance1 and zero tolerance with P<1 are
unattainable. Impossibility semantics requires admissibility; invalid input also
returns none. Minimality concerns the geometric majorant, not the actual quota
budget or collector success probability. No polynomial complexity is asserted.

For j<n and 0<=p_i<=1 below n, the selected K for the diagonal product gives
quota deficit<=epsilon when K*(n-j)<=T. Absorbed states have zero deficit.
For A=finiteProductLower(E,G), both qualification of G and explicit budgets
3*K<=(E.plan w).budget on every w in G remain required. The tolerance applies
only to the root quota. Exact child bounds and finite ProtocolPlan microseed
laws and decoders are unchanged.

With m=W(G), (1-epsilon)*m<=averagedBound<=successProbability and
1-successProbability<=1-m+m*epsilon. The excluded mass is outside G, which need
not be all qualifying tapes. For m>0 and epsilon<1, positive_mass_extracts yields
a positive-joint-mass tape/microseed pair, successful acquireCompressedFork,
ForkProvenance and extractCompressed returning a witness or generator relation.

## Independent public verification

Checks cover strict Lake build, all discovered public unittest with live mode,
metadata and catalog consistency, and one transitive union audit of AxiomAudit.
Only propext, Classical.choice and Quot.sound are allowed. No native_decide,
sorry or custom axioms. Exact counts, commands and fingerprints are recorded in
the annotated tag and external release receipt. The 39 new IO scenarios run
inside the live tests, not as additional unittest cases.

Regressions include invalid and boundary inputs, equality and the preceding K,
insufficient budgets, absorbed states, depth0/depth1 plans, empty and zero-mass
sets, a strict subset of qualifying, actual acquisition and extraction. With
n=2, p_i=1/2 and epsilon=2/5, geometric K=4 requires8 probes whereas quotaLower
already has deficit5/16 at T=4 (and deficit1/2 at T=3).

The memory-safe proof of an existing threshold regression already published in
v0.7.30 is retained byte-for-byte. Verification uses a bounded-memory sequential
runner and preserved incremental cache. This is not a new full beta checkpoint:
Lake stays0.7.1 and public beta2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1)
is unchanged. No new collector, extractor, ROM theorem, hardware run or new
module index is claimed.

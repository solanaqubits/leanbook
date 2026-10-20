# v0.7.30 — Geometric quota deficit bounds

This scoped release exports epsilon226,
`Verification.CryptoHiddenScalarQuotaDeficitContract.lean`, from private source
`9a99bfc43d099576f7b51355945c3264dafd7274`. It contains 228 direct
MasterSuite imports and 272 byte-identical formal Lean sources relative to that
pinned source. Private coordination, research archives and repository history
are excluded. Apache-2.0 source licensing is retained.

## Contract

For D(T,j)=1-quotaLower(n,p,T,j), the probability ranges 0<=p_i<=1 for
all i<n imply D(T+L,j)<=D(T,j)D(L,j). If KL<=T, then
D(T,j)<=D(L,j)^K. With j<n and K(n-j)<=T, the diagonal identity gives
D(T,j)<=(1-product_{j<=i<n}p_i)^K, including the floor(T/(n-j)) corollary.
A uniform positive step margin mu gives (1-mu^(n-j))^K.
Absorbed states, K=0 and L=0 are handled explicitly.

Blocks are analytical budget partitions in the existing recursion. No block
independence, restart or discard of accumulated successes is assumed.
The inequalities are non-strict; unit quota with unit blocks agrees exactly
with quota_one, and K=1 agrees with the epsilon225 product lower bound.

Node adapters retain exact child threshold bounds. For
A=finiteProductLower(E,G), qualification and the explicit root budget >=3K
on every tape in G give

    [1-(1-A)^K] W(G) <= averagedBound <= successProbability.

Strict positivity and existing extraction additionally require K>=1, positive
mass W(G), and epsilon224 certificates. Certificates only guarantee budget >=3
and cannot replace the multiblock budget premise. Extraction returns a valid
witness or a nontrivial generator relation, with acquired-fork provenance.
The failure bound retains the mass outside G:

    1-successProbability <= 1-W(G)+W(G)(1-A)^K.

A zero diagonal product gives an uninformative geometric upper bound of 1;
it does not establish that actual acquisition is impossible.

## Verification scope

Independent public epsilon/scoped checks cover the changed module, related
batch and registry consumers, live regressions and one transitive union axiom
audit. Only propext, Classical.choice and Quot.sound are allowed; no sorry,
custom axioms or native_decide shortcuts. Exact commands, source fingerprints
and actual check counts are recorded in the release receipt and annotated tag.
The 36 IO scenarios execute inside the live tests, not as extra unittest cases.

Regressions include boundary budgets, heterogeneous profiles, the incorrect
exponent T instead of the number of blocks, and a certified budget-3 plan that
violates a two-block estimate. Real F5 depth-0 and F37 depth-1 plans use root
budget 6; the F5 collector and extractCompressed return the zero witness.
Empty and nonempty zero-mass tape sets are covered.

Lake remains 0.7.1. The last full public beta remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1); this is not a new full
beta checkpoint. Original finite ProtocolPlan microseed laws and exact-snapshot
decoders remain unchanged. No new collector, extractor, ROM theorem, polynomial
complexity guarantee, hardware run or new epsilon index is claimed.

## Bounded-memory regression proof

The existing threshold-quota regression keeps its acceptanceRate = 1 assertion
and all 19 runtime scenarios. Its proof now first establishes acceptance for
every microseed, then simplifies the filtered set before counting. This avoids
the direct finite-set intersection reduction that exceeded an 8 GiB verification
limit. The helper and original theorem use only the three allowed axioms;
no native_decide, skipped cases, or increased memory limit is introduced.
This test-only proof adjustment is additional to the epsilon226 export; the
272 sources under Verification (including Verification.lean) remain byte-identical
to the pinned private source.

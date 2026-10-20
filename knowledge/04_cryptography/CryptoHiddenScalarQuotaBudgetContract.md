---
id: CryptoHiddenScalarQuotaBudgetContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaBudgetContract.lean
novelty: not-assessed
status: reviewed
---

# Constructive minimal block budgets

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarQuotaBudgetContract.lean)

## Finite rational selector

ε227 reuses ε226. `chooseBlockCount P ε` returns the first K satisfying
(1−P)^K≤ε. For 0<P<1 and 0<ε<1 the search cap is
⌈(1−ε)/(Pε)⌉₊, justified by (1−P)^K≤1/(1+KP), without real logarithms
or floating arithmetic. Soundness, strict minimality, existence and
positivity below tolerance 1 are proved.

For admissible P in [0,1], tolerance ≥1 selects 0; P=1 and tolerance in
[0,1) selects 1; P=0 below tolerance 1 and zero tolerance with P<1 are
unattainable. Invalid P or negative tolerance also returns none.
The impossibility equivalence explicitly requires admissible parameters.
Minimality concerns the geometric majorant only: with n=2, pᵢ=1/2 and
ε=2/5, K=4 gives 8 probes, whereas the reference recursion needs only
T=4 (deficit 5/16; at T=3 the deficit is 1/2).

## Root quota and weighted extraction

For j<n, profile values in [0,1] below n, a selected K for the diagonal
product and K(n−j)≤T imply quota deficit ≤ε. Absorbed states have zero deficit.
For A=finiteProductLower(E,G), both qualification and explicit root budgets
∀ω∈G, 3K≤(E.plan ω).budget remain required. The tolerance controls the root
quota, not every child level. Exact child threshold bounds and the finite
ProtocolPlan microseed laws and decoders are retained.

With m=W(G), (1−ε)m≤averagedBound≤successProbability and failure is bounded
by (1−m)+mε. The excluded mass is outside G, not necessarily outside qualifying.
For m>0 and ε<1, positivity of averagedBound invokes the existing
positive_mass_extracts theorem: a tape/microseed pair of positive joint mass,
successful acquireCompressedFork, ForkProvenance, and extractCompressed
returning a valid witness or nontrivial generator relation.

## Evidence and limits

Regressions cover parameter boundaries, invalid inputs, equality and the
preceding index, insufficient budgets, absorption, depth 0/1 plans, empty
and zero-mass sets, strict qualifying subsets, actual acquisition and
extraction. 39 IO scenarios belong to one compound live test; a second
live test checks the suite registry interfaces.
Finite search is not a polynomial complexity claim. No ROM, hardware run,
or unconditional extraction from global acceptance alone is asserted.
Verification is scoped and preserves the prior full β baseline. Novelty
has not been assessed.

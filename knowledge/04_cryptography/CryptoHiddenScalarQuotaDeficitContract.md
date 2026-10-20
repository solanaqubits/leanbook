---
id: CryptoHiddenScalarQuotaDeficitContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaDeficitContract.lean
novelty: not-assessed
status: reviewed
---

# Geometric block bounds for quota deficits

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarQuotaDeficitContract.lean)

## Results and assumptions

ε226 reuses quotaLower from ε216 and the ε225 diagonal identity.
For D(T,j)=1−quotaLower(n,p,T,j), assuming 0≤p_i≤1 for every i<n:

- D(T+L,j)≤D(T,j)D(L,j);
- K·L≤T implies D(T,j)≤D(L,j)^K, including K=0 and L=0;
- j<n and K(n−j)≤T imply D(T,j)≤(1−∏_{j≤i<n}p_i)^K;
- the integer-division corollary takes K=T/(n−j);
- 0<μ≤1 and μ≤p_i on j≤i<n imply D(T,j)≤(1−μ^(n−j))^K.

Absorbed states n≤j have deficit 0. Linear-profile adapters use
max(0,d−iβ), β≥0, d≤1, n>0, Kn≤T and, for the power bound,
0<μ≤d−(n−1)β. Blocks only partition the existing recursion's budget
analytically. No block independence, restart or removal of retained successes
is assumed. Bounds are non-strict. Unit quota with unit blocks agrees exactly
with quota_one. Profile values at i≥n are irrelevant.

## Plans, tapes and extraction

blockLower(A,K)=1−(1−A)^K. Local quota 4/2/3 adapters retain the exact
ε221 child threshold bound; they do not replace child bounds recursively.
For A=finiteProductLower(E,G) from ε225, qualification G⊆qualifying and
∀ω∈G, 3K≤(E.plan ω).budget give
blockLower(A,K)·W(G)≤averagedBound≤successProbability.

Strict positivity and existing extraction require K≥1, W(G)>0, ε224
protocolMarginCertificate on G, qualification and the explicit 3K budget.
Certificates only guarantee budget ≥3 and cannot discharge the multiple-block
premise. The result supplies a concrete tape/microseed pair of positive joint
mass, successful acquireCompressedFork, ForkProvenance and a valid witness
or nontrivial generator relation from extractCompressed.

The failure bound retains the mass outside G:
1−successProbability≤1−W(G)+W(G)(1−A)^K.
Conditional deficit decay does not assert global success converges to 1.

## Regressions and limitations

Regressions cover absorption, insufficient budgets, K=0/L=0, products 0/1,
a heterogeneous profile, K=1, exact quota_one, the wrong exponent T,
real F5 depth-0 and F37 depth-1 plans, empty G and nonempty zero-mass G.
A certified budget-3 plan violates the two-block estimate: budget 6 is required.
A budget-6 plan exercises the actual collector and extractCompressed.

Original finite ProtocolPlan microseed laws, exact snapshots and tape weights
are preserved. A zero bound does not exclude actual success. No new collector,
extractor, ROM result, hardware execution or polynomial complexity guarantee
is claimed. Validation is scoped; exact SHAs and results are in the separate
receipt, with the historical full beta baseline unchanged. Novelty is not assessed.

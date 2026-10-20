---
id: CryptoHiddenScalarQuotaProductContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaProductContract.lean
novelty: not-assessed
status: reviewed
---

# Explicit factorized quota lower bounds

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarQuotaProductContract.lean)

## Results and assumptions

ε225 reuses quotaLower from ε216. Insufficient budget j+T<n gives zero.
At j≤n and T=n−j the value equals the product of p_i for j≤i<n;
these algebraic identities need no probability ranges. For 0≤p_i≤1 at
i<n the bound is nondecreasing in T, so the diagonal product is a lower
bound whenever T≥n−j. Absorbed states j≥n and the empty quota have value 1.

linearQuotaProduct(n,d,β) is the product of max(0,d−jβ), j<n.
For 0≤d≤1, β≥0 and T≥n it is at most quota(n,T,d,β).
The strict margin d>(n−1)β removes max. For 0<μ≤d−(n−1)β,
0<μ^n≤linearQuotaProduct≤quota. Budget growth may be stationary;
a zero margin may collapse the conservative bound.

Node adapters retain D=heavyMass(τ_s,τ_c)·B_child with the exact existing
ε221 child threshold bound. They do not recursively replace child bounds
by products. protocolProductLower is the pure quota-three diagonal,
independent of the root budget. finiteProductLower is its exact minimum
on nonempty G and zero on empty G, separate from tape weights and acceptance.

## Probability bridge

finiteProductLower≤finiteRootLower requires 3≤(E.plan ω).budget for every
ω∈G. The bound finiteProductLower·W(G)≤successProbability additionally
requires G⊆qualifying. Child budget premises are unnecessary for this
comparison because their effects are already in B_child.
ε224 certificates on G and W(G)>0 give strict positivity, a concrete
tape/microseed pair of positive joint mass, successful acquireCompressedFork,
and a valid extractCompressed result: witness or nontrivial generator relation.
Certificates supply the root budget without a duplicated premise.

## Regressions and limits

Real F5 depth-zero and F37 depth-one plans cover the diagonal, strict and
stationary budget growth, empty and absorbed states, zero margin, μ^n,
heterogeneous budgets, empty G and nonempty zero-mass G. The mandatory
budget-two counterexample has positive protocolProductLower and zero
protocolThresholdBound, also refuting an unqualified singleton minimum
comparison. The profile p=2 refutes budget monotonicity outside probability
ranges. An end-to-end fixture runs the existing collector and extractor.

Original finite ProtocolPlan microseed laws, decoders and tape weights are
preserved. A zero lower bound does not imply actual failure. No new collector,
extractor, ROM, polynomial-time or hardware claim is made. Validation is
scoped, with exact results and SHA in separate evidence; no new full beta
checkpoint. Novelty is not assessed.

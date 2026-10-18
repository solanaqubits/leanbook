# Release v0.7.16 — IPA public scalar binding

Epsilon211: CryptoBulletproofsIPAPublicScalarBindingContract.
211 direct MasterSuite imports; 255 formal Lean sources including Verification.lean,
byte-identical to private snapshot 9dc7e143c911268f839451d11fc2a62fe87a8edb.
Lake remains 0.7.1; the annotated Git tag carries the release version.

## Exact statement and extraction

PublicClaim stores U,G,H,Q,c over a prime scalar field and an additive module.
For an external unit eta, toIPA computes the basis G,H,eta*U and target Q+c*eta*U.
ValidFork requires two distinct external units eta0,eta1 and two supplied accepting
trees checked at these contexts for the same public claim. Internal nodes still
require four distinct nonzero challenge squares; the outer pair only requires
distinct values, so eta and -eta can be used even though their squares coincide.

The extracted result is either a witness a,b satisfying BOTH

    Q = multiscalar_mul(a,G) + multiscalar_mul(b,H),
    dot_product(a,b) = c,

or explicit nonzero coefficients evaluating to zero on the original G,H,U.
No generator independence or computational hardness assumption is introduced.

First reuse the existing tree extractor on both trees. A relation for G,H,eta*U
is transported by multiplying its U coefficient by eta; eta is invertible, so
nontriviality is preserved. Two witness results produce

    d = (a0-a1, b0-b1, eta0*(dot(a0,b0)-c) - eta1*(dot(a1,b1)-c)).

Subtracting the opening equations gives evaluate(d)=0. Nonzero d is returned as
a relation. When d=0, the vectors agree and (eta0-eta1)*(dot(a,b)-c)=0 gives dot=c;
substitution gives the Q opening. checkedPair verifies both contexts and outer
distinctness before extraction. checkedPair_honest proves exact honest extraction
for every depth.

## Regressions and limits

Over F5 at depth0, G=H=U=1,Q=4,c=1, the leaf (0,0) accepts for eta0=1 and (1,0)
accepts for eta1=2. No public witness exists because a+b=4 and ab=1 are incompatible.
The pair returns d=(-1,0,1), exhibiting -G+U=0. One outer tree, or repeated equal
outer challenges without the guard, cannot justify scalar binding. Equal challenges
are rejected. Honest depth1/2 examples over F101 check 4/16 leaves, and regressions
cover context corruption, coefficient scaling and both relation branches. A U=0
fixture shows that syntactic claim changes need not change the computed context.

This is deterministic algebraic extraction from supplied trees. Obtaining the
external pair from an interactive adversary, probability and complexity of doing
so, general Forking Lemma, full zero knowledge, Fiat-Shamir/ROM and asymptotic
polynomial extraction time remain outside the theorem. Existing Pedersen/range
interfaces are not replaced. No blinding layer or full-transcript simulator is
added. In a cyclic prime-order group multiple generators are algebraically dependent;
computational binding concerns finding relations. Novelty remains not-assessed.

## Public verification and export

Public scoped checks are separate from private evidence: strict incremental Lake
build, reviewed live unittest selection, one union transitive audit with strict
AxiomAudit, metadata, knowledge and whitespace checks. Actual metrics appear in the
annotated tag and release report. Allowed axioms are propext, Classical.choice,
Quot.sound. No new full beta is claimed: public basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1), private basis remains
090aed141b831aee5182197e9ea205176f361c0f.

Russian cards, SimLab, Digital Brain, source chats, simulations, private working
materials and private Git ancestry are excluded. No new module index is allocated.

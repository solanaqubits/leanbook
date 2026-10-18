# Release v0.7.13 — IPA product tapes and recursive candidate generation

This package exports epsilon207 and epsilon208: 208 direct MasterSuite imports
and 252 Lean sources, byte-identical to source snapshot
4ea630adc474c8547f281db210e59234fed398ca. Lake remains0.7.1.

## Concrete retries: epsilon207

A verifying generator rejects missing or context-invalid child responses and
requires four nonzero challenges with pairwise distinct squares. Its single-run
finite domain defines p exactly by counting successful tapes. Completed child
responses remain supplied inputs to this module.

Uniform sampling of the full product Omega^T constructs independent retries.
Counting failure prefixes derives the epsilon206 RetryBounds premise for this
particular experiment, rather than assuming it. Failure probability is(1-p)^T;
at least one success has probability1-(1-p)^T. For p>0 the expected number of
attempts until success or budget exhaustion is at most1/p. The procedure stops
at the first success and feeds the checked extractor. This is an attempt-count
bound, not a runtime bound. RetryBounds remains an input premise of the general
epsilon206 API. Repeating one shared tape does not amplify success in general.

## Recursive generation: epsilon208

An explicit Source supplies optional messages and scalar opening proposals.
It does not supply completed child trees. Each node checks the claimed context,
a common message(L,R), nonzero challenges and distinct squares. It computes each
child statement from the parent and challenge, recursively generates all children
on separate finite tapes, and checks the scalar equation in every leaf. Missing
or malformed responses cause explicit failure, never a manufactured valid child.
A depth-k fork tree has4^k leaves; vector length2^k is a different quantity.

Fixing a root tape fixes its message, challenges and child contexts. The number
of successful child tuples is then the product of their four counts. Summing over
root tapes gives the exact finite law of total probability. Child rates can depend
on the root, so unconditional marginal rates cannot simply be multiplied.

For a nonempty finite seed domain, local message density at least a and leaf
acceptance density at least b yield lowerBound(0)=b and
lowerBound(k+1)=a*lowerBound(k)^4 for nonnegative a,b, provided the recursive local
conditions hold in the computed reachable contexts. Positive a,b then give a
positive whole-tree probability. Recursion alone does not provide availability.
A bad selected leaf rejects that tape. Zero probability for the entire experiment
requires a necessary zero-rate child for every admitted root context.

The complete generated tree satisfies ValidAcceptingTree and feeds the existing
TreeExtraction API. Its ResultValid alternative is an opening of the modeled IPA
commitment OR a nonzero generator relation. It need not recover the prover's
original secret. No new blind or external dot-product equality is introduced.

## Public verification and limits

Public evidence is collected separately from private checks. The planner selects
the dependency scope; the annotated tag and report record actual executed checks.
A single combined transitive audit covers both modules and registry integration.
Only propext, Classical.choice and Quot.sound are allowed; caches are retained.
No new full beta is claimed. The full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); the private beta basis remains
090aed141b831aee5182197e9ea205176f361c0f.

Availability of accepting messages and scalar openings remains an explicit source
condition. No general Forking Lemma for arbitrary adversaries, adaptive rewind,
Fiat–Shamir/ROM, computational binding, zero knowledge, physical RNG refinement
or asymptotic polynomial-time claim is made.

No SimLab artifacts, digital-brain documents, raw chats, simulations, Russian cards,
private working materials or private Git history are exported. This publication
allocates no new module index or experiment.

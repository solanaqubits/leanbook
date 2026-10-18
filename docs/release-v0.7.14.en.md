# Release v0.7.14 — IPA node-local multi-level retries

Epsilon209: CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract.
209 direct MasterSuite imports; 253 formal Lean sources including Verification.lean,
byte-identical to private snapshot 04726f19649512c20623cb1acb6dce3605c0fa9e.
Lake version stays 0.7.1; the Git tag carries the release version.

## New behavior and exact result

Epsilon208's recursive_retry_bounds repeats the existing whole-tree experiment.
Epsilon209 inserts a bounded retry loop inside every internal node. Each attempt
has a fresh root seed and four separate recursively budgeted child tapes. It stops
at the first full success, or explicitly fails after exhausting the budget. Leaves
check scalar opening proposals against their computed contexts. Sources still
supply messages and scalar proposals; they do not guarantee available valid answers.

Successful output satisfies ValidAcceptingTree and feeds the existing tree extractor:
ResultValid means an opening in the existing IPA interface OR a nontrivial generator
relation. No external inner-product claim or new blinding factor is introduced.
The tree has 4^k leaves at depth k. Unit budgets give exactly epsilon208's success
probability (rate_single_budget).

After fixing a root seed, the four computed child contexts are fixed. Their success
counts factor on independent child tape coordinates. Averaging over roots gives the
actual composite-attempt probability p. Independent node retries then have success
probability 1-(1-p)^T. RetryBounds is derived for this concrete experiment at each
node; it remains an input premise of the abstract epsilon206 API.

## Conditional per-depth bound

Under the recursive Dense availability assumption from epsilon208, a nonempty finite
uniform seed domain and 0 <= a,b <= 1, define

    ell_0 = b,
    ell_(k+1) = 1 - (1 - a * ell_k^4)^T_(k+1).

Then, for each depth k,

    ell_k <= Pr[Success_k].

Thus ell_(k+1) compares with success at depth k+1. Here a bounds the fraction of
valid root choices with recursively available children, and b bounds leaf acceptance.
The recurrence bounds success; it need not equal the actual success probability.
Positive availability and positive internal budgets give positive lower bounds.

Actual success is monotone in node budgets. Strict growth at a fixed node, holding
its child experiment fixed, requires 0 < actual attemptRate < 1. A lower estimate
strictly between zero and one does not ensure strict actual growth: actual success
may already equal one. The saturation counterexample is retained.

## Boundaries and public verification

Correlated/reused tapes do not justify the independent product law. A failed selected
child rejects that attempt; global zero probability requires a blocked child for every
admissible root choice. Cached validity for an old child context does not automatically
transfer to a changed context. Equal contexts or a separate validity bridge could permit
reuse, but a caching and resource model is outside this contract.

Local availability remains conditional. No general Forking Lemma, adaptive adversary
rewinding, Fiat–Shamir/ROM, physical RNG/IO refinement or asymptotic polynomial-time
result is claimed. Mathematical novelty is not assessed.

Public checks are recorded separately from private evidence, with one combined
transitive AxiomAudit and relevant live tests. Allowed axioms: propext, Classical.choice,
Quot.sound. Incremental caches are retained. Actual metrics are recorded in the
annotated tag and report. No new full beta is claimed; the full public beta basis
remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1), and the private basis
remains 090aed141b831aee5182197e9ea205176f361c0f.

Russian cards, SimLab, digital-brain, raw chats, simulations, private working materials
and private Git ancestry are not exported. This release allocates no module index.

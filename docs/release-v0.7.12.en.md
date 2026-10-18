# Release v0.7.12 — IPA tree probability and bounded retries

This single release exports epsilon205 and epsilon206: 206 direct MasterSuite
imports and 250 Lean sources, byte-identical to private snapshot
602369e67aa3f38fba4bc011b058d36b12a7df2e. Lake remains0.7.1. No v0.7.13 tag is
created for this package.

## Results and exact assumptions

A finite nonempty uniform tape space and prescribed candidate generator define
the experiment. A depth-k transcript tree has4^k leaves; its vectors have2^k entries.
The whole-tree lower bound uses sequential conditional bounds on ALL previous
successful local checks, including siblings and scalar leaves. A bound on the
average acceptance rate alone does not provide these conditional bounds.
Computed child contexts are checked. Complete validity feeds the existing
witness-or-nonzero-generator-relation extractor; it need not recover the prover's
original secret. No extra blind or external dot-product equality is introduced.

For retries let F_i be the tapes on which all earlier attempts failed. Assume
0<=p_i<=1 and |F_(i+1)|<=(1-p_i)|F_i|. The probability of success before T is at
least1-product_(i<T)(1-p_i), or1-(1-p)^T for a constant bound p. The retry premises
are derived from epsilon205 local bounds on each F_i, not from marginal success
probabilities. A repeated identical bit can have marginal1/2 on every attempt
but total success1/2, so independence cannot be silently inferred.

The first-success index is earliest and persists when the budget is extended for
the same candidate sequence. Exhaustion is an explicit error, not evidence of
impossibility. The finite tail-sum identity gives E[N_T]=sum_(i<T) Pr[F_i], hence
E[N_T]<=sum_(i<T)(1-p)^i<=1/p for0<p<=1. This counts candidate-attempt rounds,
not checker calls or runtime: the wrapper invokes the checker again to materialize
the successful result. No polynomial-time conclusion follows.

## Verification and boundaries

Public-tree checks are separate from private evidence. The public planner chooses
the actual dependency scope; executed commands and metrics are recorded in the
annotated tag and report. A single transitive audit covers the combined closure;
no new full beta is claimed. Public beta remains
2419489245019fb16e32ffac641b9f88eea94126; private beta remains
090aed141b831aee5182197e9ea205176f361c0f. Only propext, Classical.choice and
Quot.sound are allowed, and incremental caches are preserved.

The conditional hypotheses are not established for arbitrary adversaries.
General Forking Lemma, adaptive rewinding, Fiat–Shamir/ROM, computational binding,
blinding, zero knowledge and asymptotic polynomial runtime remain outside scope.

No SimLab artifacts, digital-brain documents, raw chats, simulations, Russian
cards, private working materials or private Git history are exported. No new
module index or experiment is allocated by this release.

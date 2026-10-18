---
id: CryptoBulletproofsIPABoundedRetryContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPABoundedRetryContract.lean
source_sha256: e20e1ce8695f941491d7fb82829a2f8f645ea396bcf07958dc6e47ff9b490dc2
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPABoundedRetryContract.lean)

# Bounded retries of checked IPA extraction

## Model and intended statement

The previous contract gives finite whole-tree success bounds. This module asks
what repeated attempts guarantee when candidates share randomness. A finite
nonempty set C carries uniform rational mass. All attempts use the same tape w;
generate i w may depend on its entire contents, so no independence is assumed.
The original Statement is fixed for every attempt. Candidate generation is a
prescribed total Lean function, not a model of an adversary's external IO.

Let F0=C and F(i+1) be tapes in Fi where attempt i fails. RetryBounds requires
0<=p_i<=1 and |F(i+1)| <= (1-p_i)|Fi|. These are conditional bounds after ALL
previous failures, not marginal bounds. The multiplicative form remains valid
for empty Fi and does not assign a positive probability to an impossible prefix.

## Proofs and extraction connection

failure_count_bound multiplies the successive inequalities; nonnegative factors
preserve order. failure_probability_bound divides by |C|>0. The complement
success_probability_bound gives Pr[success before T] >= 1-product(1-p_i).
constant_success_bound gives 1-(1-p)^T for uniform p.

conditional_tree_retry_bounds derives RetryBounds from epsilon205 ConditionalBounds
on each Fi. Within an attempted tree those bounds in turn condition on ALL previous
successful local checks. A provided p_i must be no greater than the product of
these local factors. The cardinality partition converts the lower bound on valid
trees into an upper bound on failures. No assumption of the final retry estimate
is used. bounded_extraction_probability states the resulting probability bound
for the actual checked extraction event.

firstSuccess scans an increasing fixed sequence and stops when it finds success.
firstSuccess_some proves earliest index; firstSuccess_extend proves persistence
under budget extension. boundedExtract returns the checked extractor's result or
retryBudgetExhausted. boundedExtract_sound gives ResultValid: an opening of the
existing IPA target OR a nonzero generator relation. It does not invent an
additional blind or external dot-product equation. boundedExtract_extend preserves
the result for a fixed candidate sequence once success has occurred.

attempts increments only while no previous success exists. attempts_none and
attempts_some show counts T and i+1 respectively; attempts_le gives the budget.
expected_attempts_tail_sum proves the finite identity E[N_T]=sum_(i<T) Pr[Fi]
by exchanging finite sums of failure indicators. expected_attempts_geometric bounds
this by sum_(i<T)(1-p)^i. geometric_telescoping proves p*sum=1-(1-p)^T;
expected_attempts_le_inverse gives E[N_T]<=1/p for 0<p<=1. This counts attempts,
not operations or runtime. A candidate tree has4^k leaves for vector length2^k.

## Regression evidence and boundary cases

A four-tape example has two independent bits, success probability3/4 and expected
attempt count3/2 for budget2. A nonzero-generator honest IPA fixture realizes the
same experiment and checks the epsilon205-to-retry bridge. Tests cover first
success, budget extension, exhaustion, T=0, p=0, p=1, empty failure prefixes,
substituted original context and invalid child context.

A single shared bit repeated at every attempt has marginal success1/2 at every
index, but total success remains1/2 for any positive budget. At budget4 its
expected attempts are5/2, exceeding1/(1/2). The conditional p=1/2 premise fails
after the first failure. Thus marginal bounds cannot justify amplification or
the claimed inverse expectation bound. No rejected example is discarded.

## Limits and evidence

Only finite prescribed experiments and conditional inequalities are proved.
The module does not establish the inequalities for an arbitrary adversary,
implement adaptive rewind, prove a general Forking Lemma, Fiat–Shamir/ROM security,
computational binding, or polynomial running time. Exhaustion is not proof of
impossibility. Choosing C and the candidate generator remains an explicit model.

Integrated as CryptoFullSuite.ipa_bounded_retry. Source snapshot:
602369e67aa3f38fba4bc011b058d36b12a7df2e. Public-tree evidence is recorded separately
in the annotated v0.7.12 tag and release report. Only propext, Classical.choice and
Quot.sound are allowed; novelty is not assessed.
See [release notes](../../docs/release-v0.7.12.en.md).

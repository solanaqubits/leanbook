---
id: CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.lean
source_sha256: 4be014a6e19ac4fb1b8a1114d7031ea536d14b98ab1e0af3a0e71b219178fe43
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.lean)

# Checked IPA candidates on independent finite retry tapes

## Motivation and model

Epsilon206 proves retry estimates under conditional failure-prefix bounds.
This module derives those bounds for an explicitly constructed experiment.
It incorporates local prototype d885c8775a51c56d7b24bf2f4f96d1bef78ebc43;
private source base is602369e67aa3f38fba4bc011b058d36b12a7df2e.

Fix a prime q, a ZMod q additive module with decidable equality, a parent Statement,
a common first message (L,R), a finite list of challenges and optional completed
child-tree responses. checkedReplies rejects zero, missing replies and replies
invalid for the child statement computed from the original parent and challenge.
candidate accepts exactly four retained challenges with pairwise distinct squares.
All selected replies must be present. No missing response is replaced by a synthetic
valid tree. This refines availability semantics, not the validity of earlier theorems.

C=calls.toFinset removes duplicate entries. The one-attempt domain Omega1=samples C 4
contains all ordered draws with replacement. candidate_single_probability proves
p=|Good|/|Omega1|=successProbability C A for the computed checked replySet A.
The domain must be nonempty for normalized probability results; seven checked
replies suffice for positivity but are not needed for exact probability identities.

## Product proof and extraction

productTapes D T=piFinset (fun _ : Fin T => D) is the full finite product D^T.
product_card proves cardinality |D|^T. tapeAttempt reads coordinate i, with a
false result outside the budget. failure_prefix_product identifies epsilon206's
failure set after i attempts with a product of i bad domains and T-i full domains.
failure_prefix_count gives |Bad|^i |D|^(T-i). This counts independent tuples directly;
there is no assumed probabilistic independence or assumed RetryBounds conclusion.

failure_step_exact and good_bad_partition imply the exact contraction factor1-p.
product_retry_bounds constructs epsilon206 RetryBounds. product_failure_probability
is (1-p)^i for i<=T; product_success_probability is1-(1-p)^T.
product_expected_attempts is sum_(i<T)(1-p)^i; product_expected_le_inverse invokes
epsilon206 to give E[N_T]<=1/p for p>0. N_T counts attempts until first success or
budget exhaustion, not instructions, cryptographic queries or wall-clock time.

runProduct reuses epsilon206 firstSuccess and calls the existing checked extractor
on the selected candidate. candidate_product_retry_bounds instantiates the product
with actual four-draw candidate tapes. candidate_product_extraction_probability is
an exact formula for successful extraction, not merely for a surrogate event.
runProduct_sound preserves ResultValid: witness in the existing IPA interface OR
nontrivial generator relation. No added blind or external dot-product equation.

## Regression cases and nonclaims

Nonzero-generator honest fixtures exercise candidate checking and extraction.
Two explicit single-attempt tapes (one accepted, one rejected) give2,4,8 product
tuples and1,3,7 successes for T=1,2,3. For uniform four draws from {1,2,3,4},
p=3/32 and the two-attempt extraction probability is183/1024. The full three-attempt
space has16777216 tuples; its cardinality is proved algebraically, not enumerated.
Tests cover zero, missing/wrong contexts, equal/opposite challenges, T=0,p=0,p=1,
first-success extraction and exhaustion. diagonal_success_probability proves that
repeating one tape keeps success probability p for every positive T;
diagonal_not_amplified proves strict disagreement with1-(1-p)^T for T>=2,0<p<1.

Completed child responses still enter as inputs. Their checking does not prove their
availability or recursively sample a whole fork tree. No adaptive rewind, general
Forking Lemma, Fiat–Shamir/ROM, asymptotic polynomial time or physical randomness
claim. The finite experiment's relationship to an implementation remains separate.

## Public verification and boundaries

Public-tree evidence is recorded separately in the annotated v0.7.13 tag and
release report. Source snapshot: 4ea630adc474c8547f281db210e59234fed398ca.
Only propext, Classical.choice and Quot.sound are allowed. Novelty is not assessed.
See [release notes](../../docs/release-v0.7.13.en.md).

RetryBounds is derived for the concrete independent product experiment; it remains
a premise in the general epsilon206 interface. Recursive Source message/scalar
availability is conditional, not guaranteed for an arbitrary prover. Actual RNG,
IO, strategy access, memory and operation costs require separate refinement.
No general Forking Lemma, adaptive rewind, Fiat–Shamir/ROM or polynomial runtime
claim follows from these finite algebraic and counting results.

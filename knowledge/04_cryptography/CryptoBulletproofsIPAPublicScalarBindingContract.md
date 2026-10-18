---
id: CryptoBulletproofsIPAPublicScalarBindingContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPAPublicScalarBindingContract.lean
novelty: not-assessed
status: reviewed
---

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPAPublicScalarBindingContract.lean)

# IPA binding to an explicit public scalar

## Specification and prerequisites

`PublicClaim q A k` stores `U,G,H,Q,c`; vectors have length `2^k`.
Scalars form the prime field `ZMod q`. The additive commitment group `A` is
an `AddCommGroup` and a module over that field. No generator independence or
computational hardness is assumed.

For a unit η, `toIPA` supplies the existing extractor with generators
`G,H,η • U` and statement `Q + c • (η • U)`. `ValidFork` requires two distinct
units η₀,η₁ and two supplied trees valid at these computed statements for the
same public claim. Internal forks still require four distinct nonzero challenge
squares; the outer pair requires only distinct values. Its squares may coincide.

`WitnessValid p a b` means exactly

    Q = multiscalar_mul a G + multiscalar_mul b H,
    dot_product a b = c.

`ClaimResultValid` is this witness condition OR an explicit nonzero coefficient
vector evaluating to zero on the original basis G,H,U.

## Proof and executable interface

`pair_extraction_soundness` delegates each supplied tree to
`CryptoBulletproofsTreeExtraction.tree_extraction_soundness`.
A relation on G,H,ηU is transported by `liftRelation`: multiply its U coefficient
by η. `liftRelation_eval` preserves evaluation; `liftRelation_injective` preserves
nontriviality because η is a unit.

Two witness results yield the vector `difference`:

    d = (a₀-a₁, b₀-b₁,
         η₀(dot(a₀,b₀)-c) - η₁(dot(a₁,b₁)-c)).

`difference_eval` proves evaluation zero by subtracting the two opening equations.
If d is nonzero, `combineResults` returns it. If d is zero, the first coordinates
identify the witnesses and the last gives `(η₀-η₁)(dot(a,b)-c)=0`.
The distinct-unit hypothesis then yields the public scalar equation and Q opening
(`difference_zero_witness`). No abstract linear independence is substituted for
computational binding.

`checkedPair` validates both contexts and distinctness before extraction.
`checkedPair_success_iff` characterizes its accepted inputs; `checkedPair_sound`
proves its result. `checkedPair_diagonal`, `checkedPair_reject_left` and
`checkedPair_reject_right` describe rejection. `checkedPair_honest` proves exact
witness recovery from honest supplied trees at every depth.

## Counterexamples and verification scope

`Counterexample.claim` uses ZMod5, depth0, G=H=U=1, Q=4,c=1.
At η₀=1 the leaf (0,0) accepts; at η₁=2 the leaf (1,0) accepts.
There is no public witness: a+b=4 and ab=1 have no solution in this field.
The checked pair instead returns d=(-1,0,1), the relation -G+U=0.
Repeating η₀ without the distinctness guard would return an invalid witness;
the checked interface rejects it.

Regressions in `tests/lean/ipa_public_scalar_regression.lean` exercise honest trees
of depths1 and2 over ZMod101, 4 and16 leaves, the outer pair η and -η, scaling,
both relation branches, mismatched Q/c/U and swapped contexts. A U=0 fixture
preserves computed context despite a changed c: syntax changes alone do not imply
context rejection. Formal examples use kernel reduction, not native-decide axioms;
IO checks are separate computational evidence. Scoped checks use the public
verifier CLI and the union AxiomAudit; no new full beta checkpoint is claimed.

## Provenance, applications and limits

This extends the existing vector-tree extractor rather than the retry/cache APIs.
The design history corrected the suggestion that appending cU to one equation
alone forces the extracted dot product to equal c. The two outer accepting trees
remain supplied inputs. Their interactive acquisition, probability, computational
cost, general Forking Lemma, Fiat–Shamir/ROM and an asymptotic argument of knowledge
are not established.

Existing range-reduction and Pedersen modules already contain blinding and
separate opening interfaces. This module adds no blinding or ZK simulator. Perfect
hiding requires uniform message-independent masking with a bijective mask action,
not algebraic independence of generators. In a cyclic prime-order group multiple
generators are algebraically dependent; hardness concerns finding relations.

A possible application is an outer-challenge binding layer for an interactive
IPA transcript collector. It must supply both trees for one public claim and
establish the unproved probability/complexity bridge. Applications remain
hypotheses and mathematical novelty remains `not-assessed`. Private research and evidence materials are excluded from the public export.
See [release notes](../../docs/release-v0.7.16.en.md) for the public verification scope.

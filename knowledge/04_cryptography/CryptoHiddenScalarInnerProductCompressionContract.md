---
id: CryptoHiddenScalarInnerProductCompressionContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarInnerProductCompressionContract.lean
novelty: not-assessed
status: reviewed
---

# Hidden inner-product compression: single execution and supplied forks

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarInnerProductCompressionContract.lean)

## Exact interface and messages

The public Claim and WitnessValid are reused from epsilon213, over ZMod q with q
prime and an additive scalar module. Claim already contains G,H,B,J,U,P,V.
The witness opens P=M(a,b) and V=dot(a,b)B+rho J. P is not claimed hiding.

The prover sends A,T0,T1, receives e (zero allowed), and sends t=dot(l,m),z.
Only then does the verifier choose a unit eta. With Qe=A+eP and Ueta=eta U,
the IPA target is Qe+t Ueta. Each round sends L,R BEFORE receiving a fresh unit x;
finally two scalars are sent. Full response vectors are absent from the wire.
`compress` calls the existing executable IPA prover on l,m and the given calls.
Neither the original witness nor the original protocol masks are inputs to compress.

`compressedVerify` checks t B+z J=T0+e T1+e^2 V and the existing IPA verifier on
the computed target. `compress_complete` works for every valid full transcript,
not just one test witness. `honest_compressed_complete` composes epsilon213.
No blinding bijection, hardness or finite target is required for completeness.
`compression_prefix` proves announcements/e/t/z independent of eta and inner calls.
`prover_prefix_causal` proves round j depends only on calls strictly before j.

## Operational law and exact HVZK

`sequentialIPA` constructs the current round message, samples x, folds the state,
and recurses. `challengeTape` draws independent calls recursively.
`sequential_ipa_eq_tape` proves equality with the existing prover on that tape.
`sequentialCompression` fixes t,z before sampling eta. `honestExecution` samples
fresh masks first, then the independent outer challenge, eta and inner calls.
`honest_execution_eq_postprocessing` identifies this operational law with the
full honest interaction bound to `compressionKernel`. The law may be nonuniform;
the fixed eta/inner laws make these samples independent. `uniformChallenges` is
the independent uniform specialization, not a claim about adaptive verifiers.

For ANY common mu on eta and the whole inner-call sequence,

    realView.bind (compressionKernel p mu) = seededSimView.bind (compressionKernel p mu).

`compressed_hvzk` obtains this exact PMF identity from epsilon213 under the local
hypothesis that x -> x J is bijective. Correlations within mu do not invalidate
postprocessing equality, but the sequential independent-law identity has its own
explicit premises. `execution_hvzk` combines both statements. `seededCompressedSimulator`
is executable: it runs the old seeded simulator then the honest IPA prover,
without a discrete-log inversion. Acceptance alone is not the HVZK argument.
The witness rho is fixed; uniform fresh randomness belongs to the protocol masks.

## Extraction: six trees are not a transmitted proof

`CompressedFork` contains one common A,T0,T1 and three nodes. Each node fixes e,t,z
and provides two IPA trees at distinct unit eta values for PublicClaim(A+eP,t).
`ValidCompressedFork` checks distinct outer e, the scalar equation, and both
computed tree contexts including every internal four-distinct-square condition.

`extractCompressed` prioritizes the first internal relation. `pair_extraction_soundness`
from epsilon211 gives either l,m with M(l,m)=A+eP and dot(l,m)=t, or a relation on
G,H,U. The latter is transported by epsilon212 liftRelation with zero B,J coefficients.
When all three pairs yield witnesses, `recovered_fork_valid` supplies epsilon213's
ValidFork and `three_point_extraction_soundness` returns its joint witness OR
outer relation. `compressed_extraction_soundness` proves the final ResultValid.
There is no need to manufacture epsilon212 ValidBundle or a linear Pedersen fork.
Extraction does not assume bijective blinding or computational hardness.

`checkedExtract` exposes success iff ValidCompressedFork and soundness.
`fork_from_full_valid` constructs valid honest trees from a supplied valid full fork;
`extract_from_full` proves exact agreement with the outer extractor, using the
existing honestTree_exact theorem instead of opaque array reduction.
`accepting_tree_compression` maps a matching path of a valid tree to an accepted
single compressed transcript. The converse is not asserted from one path.

For depth k the six trees have 6*4^k leaves; they are algebraic extractor inputs.
`compressed_payload` counts 2k+3 prover group elements and four prover scalars,
excluding verifier challenges and public inputs. This counts elements, not bytes,
group operations, machine runtime or a polynomial-time adversarial extractor.

## Regressions and boundaries

Honest lengths 1,2,4 over F11 use internal units 1,2,3,4 with squares 1,4,9,5.
Tests check exact witness recovery and all 96 leaves at depth2, zero challenge,
causal prefix invariance, payload counts and executable simulation for all 11 calls.
Two relation cases are separate: an internal epsilon211 F5 depth0 countermodel
and an outer nonaffine response triple over F11 with honest inner trees.
Tests reject failed scalar equations, repeated e/eta, wrong tree contexts and
altered announcements. At e=0, changing public P,V can preserve the computed
checks; syntactic change alone is not an unconditional rejection theorem.
Generic exact PMF equalities are instantiated independently of runtime checks.

This is single-path honest-verifier simulation and algebraic soundness for supplied
forks. Acquiring the six trees from an adaptive adversary, knowledge-error bounds,
malicious-verifier ZK, Fiat-Shamir/ROM, DLog hardness reductions and formal
polynomial-time guarantees remain outside the result. No new full beta is claimed.
Novelty remains not-assessed. The pinned source and public verification scope are
recorded in the [release notes](../../docs/release-v0.7.19.en.md).

---
id: CryptoHiddenScalarInnerProductProtocolContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarInnerProductProtocolContract.lean
novelty: not-assessed
status: reviewed
---

# Hidden inner product with full vector responses

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarInnerProductProtocolContract.lean)

## Exact relation and protocol

Scalars are ZMod q with q prime; the target is an additive group/module A.
Vectors have length 2^k, reusing the existing IPA types and extended generator
record. U is unused by this uncompressed protocol. Write M(a,b)=MSM(a,G)+MSM(b,H),
B=generators.B and J=generators.Hblind. Claim contains generators,P,V; Witness
contains a,b,rho, with M(a,b)=P and dot(a,b) B+rho J=V. Neither the scalar nor its
opening is public. The public P itself is not claimed to be a hiding commitment.

Commit samples independent uniform s,t,tau0,tau1 and sends
A=M(s,t), T0=dot(s,t) B+tau0 J,
T1=(dot(s,b)+dot(a,t)) B+tau1 J.
For any field challenge e, respond with l=s+e a, m=t+e b,
z=tau0+e tau1+e^2 rho. Verify checks exactly

    M(l,m)=A+e P
    dot(l,m) B+z J=T0+e T1+e^2 V.

`honest_completeness` follows from `dot_expansion`. It needs no finite target,
nonzero generator, bijective masking or computational hardness. Zero challenge is
allowed; it returns fresh masks, not the witness. Honest challenge independence
is explicit in the interaction law, not inferred from message syntax.

## Three-point extraction

`ValidFork` requires three Verify predicates, the SAME three announcement elements,
and pairwise distinct challenges. An injective Fin 3 challenge family entails
sufficient field size; there is no vacuous assertion of such a family over F2.
`candidate` computes vector slopes from points 0,1, and the top coefficient of z
using the existing `CryptoBulletproofsWitnessExtraction.interpolate_quad`.
`deviation` measures the third vector responses against these affine candidates.

`candidate_linear` and `masks_linear` give the P and A equations. If the third
response is nonaffine, `deviation_linear` gives a nonzero (G,H) relation embedded
as (g,h,0,0,0) in the existing RelationCoefficients. Otherwise `responses_affine`,
scalar interpolation and `quadratic_module_top` recover the V equation. The last
lemma is module-valued coefficient extraction, not an unproved generator
independence assumption. `three_point_extraction_soundness` proves the resulting
witness-or-relation dichotomy. `checkedExtract` rejects invalid forks; its success
iff and soundness theorems expose the exact checking boundary.

No masking bijectivity is required for extraction. A relation branch does not mean
that all valid witnesses are absent. Acquiring three common-prefix executions
from an adversary and bounding their acquisition cost are separate obligations.

## Exact full-transcript honest-verifier simulation

This block assumes precisely Function.Bijective (fun x => x • J). In a group of
cardinality q over Fq, J nonzero suffices by the existing Pedersen lemma; it is not
sufficient in an arbitrary higher-dimensional module.

For fixed e, the simulator samples independent uniform l,m,z,T1 and computes
A=M(l,m)-e P and T0=dot(l,m) B+z J-e T1-e^2 V. `simulator_accepts` alone is only
acceptance. The stronger proof `simulate_honest` identifies entire transcripts.
`hvzk_randomness_bijection` maps honest randomness to (l,m,z,T1). Its triangular
inverse recovers s=l-e a,t=m-e b, then tau1 via the inverse blinding map, then
tau0=z-e tau1-e^2 rho. The secret witness and inverse map occur only in
this equality proof; they are not simulator inputs.

`seededSimulator` is executable and samples T1=theta J, so it performs no discrete
logarithm inversion. `real_view_eq_seeded_sim_view` proves exact PMF equality for
every valid fixed witness and every fixed e. Its public statement does not need
an additional Fintype A assumption: bijective masking supplies finiteness for the
proof. `interaction_hvzk` mixes by an independently sampled honest challenge,
preserving the actual order of honest messages. It compares joint transcripts,
not merely acceptance or separately uniform marginals.

The original opening rho is fixed, not resampled. Uniform freshness refers to
protocol masks. HVZK is relative to the fixed public P,V, not a claim that these
public inputs conceal every property of the witness. Polynomial-time models,
malicious-verifier ZK and Fiat-Shamir/ROM are not established.

## Regressions and corrected specifications

The kernel and runtime regression file checks honest extraction at lengths 1,2,4
over F5 including challenge zero, both extraction branches, repeated challenges,
changed shared announcements, changed response, P and V, and the executable
simulator for all five field challenges. The generic PMF theorems are instantiated.

The two-point polynomial perturbation e(e-1) vanishes at 0,1 but not at 2. This is
coefficient ambiguity when coefficient data may differ, NOT an impossibility
result for any two-transcript extractor under fixed announcements and statement.

The J=0 countermodel fixes ONE claim P=3,V=2,G=H=B=1 over F5 and witnesses
(a,b,rho)=(1,2,0),(2,1,0). At e=0, the transcript with s=1,t=0 has T1=2 for the first
witness, but no mask for the second witness generates that entire transcript.
`degenerate_views_differ` proves different real transcript PMFs via support. This
is stronger and more precise than merely showing a nonhiding commitment. A
separate F5^2 example shows nonzero J=(1,0) is not surjective.

Earlier proposed responses c+e rho did not match A+e V, and an e^2 mask in a
linear-opening equation contaminated its two-point extraction. Merely passing a
separate zc or an accepted IPA path did not bind the same dot product. This module
uses a direct quadratic commitment equation and a three-point fork instead.

## Integration, evidence and open bridges

Registered as CryptoFullSuite.hidden_scalar_protocol and audited through the
common AxiomAudit. See [release notes](../../docs/release-v0.7.18.en.md) for the pinned source and public verification scope. No new full-beta checkpoint is claimed.

This is a separate full-vector interactive layer. It does NOT derive the epsilon212
ValidBundle from two paths and does not yet provide logarithmic IPA compression.
It reuses existing relation formats and interpolation without changing those APIs.
A possible application is a reference verifier against which a future compressed
protocol is proved correct and distribution-preserving; that bridge is unproved.
No DLog hardness, knowledge-error reduction, adversarial rewinding, general Forking
Lemma, ROM, malicious-verifier ZK or formal polynomial-time guarantee is claimed.
Mathematical novelty remains not-assessed.

# Release v0.7.18 — Hidden inner-product protocol and exact HVZK

Epsilon213: `CryptoHiddenScalarInnerProductProtocolContract`.
213 direct MasterSuite imports; 257 formal Lean sources including Verification.lean,
byte-identical to source snapshot 6a1e1c2d5ac5ebaa74b177c651114c01c44857a7.
Lake stays 0.7.1; the annotated Git tag carries the release version.

## Public relation and honest protocol

The scalar field is ZMod q for prime q; the target is an additive group/module.
Vectors have length 2^k. Write M(a,b)=MSM(a,G)+MSM(b,H), B for the value generator,
and J for the blinding generator. Public Claim contains generators,P,V; a valid
Witness contains a,b,rho such that

    M(a,b)=P, dot(a,b) B+rho J=V.

Neither c=dot(a,b) nor rho is a public protocol input. The existing extended
basis type is reused; U is unused in this uncompressed layer. No hiding property
of the public vector commitment P is claimed.

The prover chooses fresh independent uniform s,t,tau0,tau1 and announces

    A=M(s,t)
    T0=dot(s,t) B+tau0 J
    T1=(dot(s,b)+dot(a,t)) B+tau1 J.

For a field challenge e, it responds with l=s+e a, m=t+e b,
z=tau0+e tau1+e^2 rho. The verifier checks

    M(l,m)=A+e P
    dot(l,m) B+z J=T0+e T1+e^2 V.

`honest_completeness` holds for every challenge, including zero, and every mask.
It needs no bijective blinding, finite target or computational hardness premise.
At zero challenge the answers are fresh masks, not the original witness.

## Three-point algebraic extraction

`ValidFork` requires three accepted transcripts with common A,T0,T1 and pairwise
distinct challenges. Slopes from the first two responses give candidate a,b and
masks s,t. The deviation of the third response from these affine lines either
produces a nonzero relation on G,H or is zero. In the latter case, quadratic
interpolation extracts rho and proves V=dot(a,b) B+rho J.

`three_point_extraction_soundness` returns a joint witness OR explicit nonzero
`RelationCoefficients` with zero `relation_eval`. This uses no generator
independence or blinding-bijectivity assumption. `checkedExtract` rejects invalid
forks, and its success characterization and soundness identify the exact boundary.
A relation result does not assert that every possible witness is absent.

## Exact full-transcript HVZK

Only the simulation block assumes that x -> x J is bijective. Nonzero J implies
this in the appropriate prime-order group; it does not suffice in arbitrary
modules. The original witness rho is fixed; fresh randomness belongs to the
protocol masks. For a fixed challenge e the simulator samples independent uniform
l,m,z,T1 and reconstructs A=M(l,m)-eP and
T0=dot(l,m)B+zJ-eT1-e^2V.

`simulate_honest` establishes equality of entire transcripts under an explicit
triangular randomness bijection. `real_view_eq_sim_view` proves exact PMF equality,
including all message correlations. The executable `seededSimulator` samples
T1=theta J from a uniform scalar and performs no discrete-log inversion.
`real_view_eq_seeded_sim_view` proves its exact law. `interaction_hvzk` mixes over
an independently sampled honest challenge and preserves the honest message order.
The inverse blinding map and the witness occur only in the proof of the bijection,
not as simulator inputs.

## Regression evidence and limits

Finite examples over F5 cover honest lengths 1,2,4, both extraction branches,
challenge zero, repeated challenges, altered announcements/responses/P/V, and
executable simulation for all five challenges. Generic PMF identities are tested
by theorem instantiation. The polynomial e(e-1) demonstrates two-point coefficient
ambiguity when coefficient data may vary; it is not a universal impossibility
claim for every two-transcript extractor with fixed announcements and statement.

For J=0, one fixed claim P=3,V=2,G=H=B=1 has two valid witnesses (1,2,0),(2,1,0)
whose real transcript PMFs differ. The support proof `degenerate_views_differ`
concerns the full view at the same public claim, not merely commitment hiding.
A separate F5^2 example shows a nonzero J can fail surjectivity.

This is a full-vector interactive reference protocol with linear-size responses.
IPA compression and a bridge to epsilon212 ValidBundle remain unproved. Acquiring
three common-prefix accepting transcripts from an adversary, general Forking Lemma,
malicious-verifier ZK, Fiat-Shamir/ROM, DLog hardness reductions and formal
polynomial-time guarantees are outside this result. Mathematical novelty remains
not-assessed.

## Public verification and export

Public epsilon/scoped evidence is generated independently of private evidence:
strict incremental Lake build, addressed live unittest, one union transitive
audit with strict AxiomAudit, metadata, knowledge and whitespace checks. Actual
metrics are recorded in the annotated tag and release report. Allowed axioms:
propext, Classical.choice, Quot.sound. The preserved full public beta is
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); no new full beta is claimed.

The explicit export includes the module, integration, addressed tests, metadata
and English documentation. Private Git ancestry, Russian cards, SimLab, Digital
Brain, simulations, chats and working artifacts are excluded. This release
allocates no new module index and starts no further research task.

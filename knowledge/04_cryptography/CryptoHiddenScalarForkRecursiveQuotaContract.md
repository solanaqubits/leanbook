---
id: CryptoHiddenScalarForkRecursiveQuotaContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarForkRecursiveQuotaContract.lean
novelty: not-assessed
status: reviewed
---

# Recursive snapshot quota bounds

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarForkRecursiveQuotaContract.lean)

## Statement and concrete law

`TreePlan.probability_lower` proves a bottom-up bound for the actual epsilon215
`acquireTree`. At depth zero it checks the packet is a leaf and the exact
`ValidAcceptingTree` predicate; malformed or rejected leaves have bound zero.
At a round, primitive query failure contributes zero; success recursively uses
`Observation.after`, the returned packet and `child_statement`.

For each node, the full-probe density d is the average of these computed child
quota-completion bounds. The node bound is delta=quotaLower(n,p,T,0), where
p(j)=max(0,d-j*beta). Only delta is passed to the parent. The quotas are 4 inside
IPA, 2 at eta and 3 at e. `EtaPlan.probability_lower` bounds the existing eta
collect loop; `ProtocolPlan.probability_lower` bounds actual compressed acquisition,
including initial abort, unexpected packets and failed scalar equations.
`ProtocolPlan.positive_extracts` composes positive probability with existing
provenance and witness-or-nontrivial-relation extraction. No new collector or
extractor is introduced; no internal subtree success bounds are assumed.

The implemented law uses independent finite uniform microseed blocks and a
common seed shape and budget at each depth. `CallLaw.call` depends on the full
snapshot, including history and memory. Repeated preimages retain their weights;
`CallLaw.mass` proves the beta bound for key fibers (squares at IPA, equality at
eta/e). Child schedule decoding uses the actual observed child snapshot. The
same shape does not mean independent call marginals inside a full probe: a
child call decoder may depend on the parent call through its resulting snapshot.
Arbitrary real-weight laws, variable per-snapshot seed cardinalities/budgets and
a general dependent-sigma law adapter are outside this concrete contract.

The schedule decoder evaluates deterministic model queries to compute snapshots;
this pure evaluation is not counted as a second acquirer ResourceTrace. The
resource trace belongs to the executed epsilon215 acquirer. No total runtime or
polynomial-time claim for law construction or decoding is made.

## Regression evidence

The positive depth-one example is over F37. Calls 1 through 8 have eight distinct
nonzero squares, eta uses four units, and e uses 32 distinct field elements.
Exact class masses are respectively 1/8, 1/4 and 1/32. Budgets are 4,2,3:

| Level | d | delta |
| --- | --- | --- |
| IPA | 1 | 105/256 |
| eta | 105/256 | 4305/65536 |
| e | 4305/65536 | 2030724465/281474976710656 |

The numerator is 4305*2257*209=2030724465. The submitted 2030720085 was an
arithmetic error and is not a verified value. Field calls and all rational
identities are checked with trusted-kernel decisions, not native_decide.
An explicit decoded schedule runs real acquisition at depths 0,1,2. Increasing
depth with the same small budgets need not preserve a positive bound.

Further regressions exercise actual collect with 3 accepting calls among 5:
three independent probes succeed with exact probability 6/125, while the valid
loose beta=3/10 gives lower bound zero. Two reachable snapshots of one model have
equal algebraic context but leaf acquisition probabilities 1 and 0. A biased
repeated seed schedule violates the advertised law and returns exhaustedE with
a nonempty trace. A real acquired fork is passed to the existing extractor;
initial abort preserves Q=1,R=0 and zero bound.

## Limits

This is finite algebraic/probabilistic reasoning relative to one modeled tape
and exact snapshots, not an external-process refinement. Primitive behavior and
finite law/class-mass conditions remain explicit. Global acceptance does not
supply these laws automatically. No ROM/Fiat–Shamir, general Bellare–Neven,
cryptographic hardness or polynomial complexity result is asserted. Existing
Clean-only exact resource formulas and schedule bounds remain unchanged.
Only epsilon/scoped verification is claimed; full beta baselines remain historical.

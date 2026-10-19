---
id: CryptoHiddenScalarSinglePathContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarSinglePathContract.lean
novelty: not-assessed
status: reviewed
---

# Single causal path and heavy prefixes

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarSinglePathContract.lean)

## Executable model and theorem

`execute` uses the existing epsilon215 `AdversaryModel`, fixed tape, `query`,
`Observation.after` and exact snapshots. It produces one compressed transcript,
not a fork. The order is commit, outer e, binding eta, then inner challenges;
the packet received at a round precedes that round's challenge. At depth zero,
eta returns the final leaf. No input witness, accepting tree or supplied validity
predicate is used. `runIPA` carries the actual folded context and computes the
terminal scalar check; the outer scalar check is conjoined with that result.

Raw execution returns `none` for primitive aborts and unexpected packet shapes.
It collects a syntactically complete transcript even if a scalar/leaf equation
fails: these runs have `accepted=false`. Checks are not an early-stop policy;
no resource refinement of an early-stopping external verifier is asserted.
`accepted_iff_verifies` proves:

`AcceptedRun p claim model seed ↔ ∃ tr, ProducedTranscript p claim model seed tr ∧ compressedVerify claim tr`.

`produced_provenance` proves `SinglePathProvenance` for every produced transcript,
including rejected complete transcripts. It records actual transition equations
and reachable snapshots at every boundary. It is distinct from `ForkProvenance`.
`observation_unique`, `announcement_prefix` and `scalar_prefix` prove that a fixed
model/state/request cannot change an observation, the initial announcement is
fixed across paths, and equal e fixes t/z before eta and subsequent challenges.

## Finite laws and cuts

The plan reuses epsilon219 `CallLaw` and `TreePlan` shapes. `PathSeed` uses one
uniform independent microseed per round; `SinglePathSeed` adds one e and one eta
seed. Acquisition retry budgets are intentionally unused. Call decoders depend
on the exact snapshot, so decoded calls need not have independent marginals.

`TreeCut.split` is an explicit equivalence between full inner seeds and a prefix /
suffix product at any round boundary. `afterESplit` and `afterRoundSplit` expose
the corresponding full-protocol cuts (the latter includes the boundary immediately
after eta and the terminal boundary). Each seed occurrence is retained, even
when several seeds decode to one call. There is no uniformization of decoded
images or conditioning on already accepted prefixes.

`acceptance_eq_prefix_average` proves exact equality of global acceptance and the
uniform average of `continuationRate`. It uses epsilon218 `product_event_average`
and an explicit cardinality-preserving bijection. The generic theorem accepts
any supplied product equivalence; chronological interpretation applies to the
provided chronological cuts, not arbitrary re-encodings.

`heavy_prefix_lower` reuses the existing finite heavy-prefix lemma:

`max(0,(acceptanceRate-theta)/(1-theta)) ≤ heavyFraction`, for `theta<1`
and a nonempty prefix space. `continuation_range` also handles an empty suffix
space with the existing probability convention. `heavy_prefix_has_execution`
requires `theta>0`: a heavy prefix then has an actual accepted continuation with
provenance. A zero threshold cannot exclude failed rows.

## Regressions and limits

Kernel and runtime regressions cover depths 0/1/2, e=0, abort and wrong packets at
all stages, rejected complete transcripts, actual snapshot-dependent round decoding,
canonical seed cuts, and repeated e preimages. In the finite F5 example, three
microseeds decode to [0,0,1]; only e=0 continues. Exact acceptance and the heavy
fraction at theta=1/2 are 2/3, while the conservative lower bound is 1/3.
Equal weighting of the decoded set would incorrectly give 1/2.

No runtime or resource count is claimed for this new single-path runner. Existing
acquisition resource bounds are unchanged. This result does not infer child quota
completion probabilities from single-path acceptance, build fork trees, resample
adversary tapes, implement Fiat–Shamir, or prove external-process/hardware behavior.
Random-tape averaging and recursive threshold-to-quota composition remain separate.
Only scoped verification is claimed; full beta baselines remain historical.

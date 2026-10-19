# v0.7.22 — Independent full-probe schedule progress

This scoped release exports epsilon217,
`CryptoHiddenScalarForkScheduleProgressContract`, from private snapshot
`3e8b700ffda5c13c3e1ea49731465bda1fd5f708`.
The registry contains217 direct MasterSuite imports and261 formal Lean sources.
Lake's package version remains0.7.1. The last full public beta baseline remains
`2419489245019fb16e32ffac641b9f88eea94126`; no new full beta checkpoint is claimed.

## Proved contract

For a nonempty finite microseed set C, independent uniform full probes C^T,
coherent successful keys, full-probe success mass at least d (0<=d<=1), and
per-key-class mass at most beta (beta>=0), the existing collector satisfies
ProgressBounds with p(j)=max(0,d-j beta). Each seed includes its complete child
schedule. j counts retained successful distinct classes; beta is not a depth
or budget penalty. Success and class need not be independent.

An exact coordinate-resampling involution proves freshness; the actual scan prefix
is invariant under replacing its next coordinate. Blocking retained classes loses
at most j beta mass. The existing epsilon216 quota recurrence yields success bounds;
exact snapshot adapters cover quotas4/2/3. A positive bound supplies an actual sampled
schedule, provenance and the existing witness-or-generator-relation extraction result.
No new collector or extractor is introduced.

Regressions distinguish replacement and without-replacement sampling, weighted seed
images, correlated repeats, retries after failure and successful-only duplicate
blocking. F11/F7 square-class examples and depth-one acquisition exercise the bridge.

## Scope and validation

Public checks are performed independently: warning-as-error Lake build, live tests,
one transitive declaration audit with strict AxiomAudit, metadata and knowledge
checks. Only propext, Classical.choice and Quot.sound are allowed. Detailed measured
results are recorded in the annotated tag and commit after the checks pass.

Local full-probe density remains an explicit premise. No arbitrary-adversary
acceptance-to-density theorem, general Bellare–Neven lemma, ROM/Fiat–Shamir,
external-process refinement or polynomial-time guarantee is established.
The without-replacement sampler is a regression comparison, not a universal adapter.
ResourceTrace and schedule bounds are unchanged: Q(k)=4+2(4^(k+1)-1),R(k)=Q(k)-1
are exact only for Clean successful traversals; InitialAdversaryAbort hasQ=1,R=0.

Export includes the Lean module and integration, targeted tests, batch metadata
and English documentation. SimLab, Digital Brain, Russian cards, raw chats,
simulations and private working artifacts are excluded.

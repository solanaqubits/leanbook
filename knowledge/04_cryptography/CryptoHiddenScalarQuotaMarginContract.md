---
id: CryptoHiddenScalarQuotaMarginContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarQuotaMarginContract.lean
novelty: not-assessed
status: reviewed
---

# Decidable quota margins and a positive finite minimum

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarQuotaMarginContract.lean)

The recursive certificate checks the existing plan, not adversary acceptance.
Leaves impose no quota. Each node requires its child certificate, T≥n and
(n−1)β < heavyMass(parent cutoff, child cutoff) times the existing child threshold
bound. The quotas are4/2/3; depth0 skips quota4. The existing epsilon218 positivity
lemma proves strict positivity of the computed threshold bound.

finiteRootLower is executable: zero on an empty set of tapes, the exact minimum
of protocolThresholdBound on a nonempty set. Certificates on every member make
this minimum positive. No weights or acceptance predicates enter its definition.

For a subset G of qualifying tapes with positive original weight, the contract
proves0 < finiteRootLower·W(G) ≤ averagedBound ≤ successProbability. Nonemptiness
alone is insufficient: all its tapes could have zero weight. The existing extractor
then supplies a valid witness or a nontrivial generator relation on an actual
successful acquisition with positive joint tape/seed mass and fork provenance.

The global adapter additionally requires all root cutoffs≤theta<1, weighted
acceptance≥alpha>theta, and certificates on qualifying tapes. Heavy-tape bounds
supply positive qualifying mass. Global acceptance alone does not imply extraction.
A positive arithmetic bound may coexist with an aborted, nonqualifying tape.
Zero conservative bounds do not imply impossible actual success.

Original per-tape ProtocolPlan microseed laws and decoders are unchanged. No new
collector, extractor, diagonal bound, ROM theorem, polynomial complexity claim or
hardware experiment is introduced. Novelty is not assessed. Regressions cover
actual F5 depth0 and F37 depth1 plans with valid class mass bounds, varying budgets,
empty and zero-mass sets, failed margins, aborts and executable F5 extraction.
Verification is scoped; exact results and source pins are recorded separately.

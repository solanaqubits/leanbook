---
id: AxiomAudit
language: en
section: verification
source: Verification/AxiomAudit.lean
source_sha256: 91acec1f78c5244f953c77c9516bad17295af6b3022b00a9993c3992fc2a99dd
novelty: not-assessed
status: reviewed
---

# AxiomAudit

[Section](README.md) · [Lean source](../../Verification/AxiomAudit.lean)

## Verified result

The #audit_axioms command rejects disallowed transitive axioms of a selected declaration, including sorryAx.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

[Read the declarations](../../Verification/AxiomAudit.lean)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.

Module 191 adds `QuantumQutritDecoderCircuitRefinement.verification_suite` through
`QuantumPhysicsFullSuite.qutrit_circuit_refinement`; see the
[beta 0.7 release](../../docs/release-v0.7.0.en.md).

`DistributedSystemsFullSuite.tendermint_slashing` connects certified offender
attribution to exact rational slashing and conditional honest-share growth.
[Contract](../02_distributed_systems/DistributedTendermintSlashingPenaltyContract.md).

Module 193 adds `CryptoFullSuite.pedersen_opening`: two-branch opening extraction and conditional composition with module 178.

Module 194 adds `DistributedSystemsFullSuite.tendermint_replay`: sequential replay protection and conserved ledger accounting.

Module 195 adds `DistributedSystemsFullSuite.tendermint_unbonding`: finite queues, inclusive evidence windows, two-phase slots and conserved accounting.

Module 196 adds `DistributedSystemsFullSuite.tendermint_epoch_identity`: historical resolution, stable global identities and preserved cross-epoch liabilities.

Module 197 adds `DistributedSystemsFullSuite.epoch_quorum`: weighted honest quorum intersection across epochs, with strict and non-strict threshold conventions.

Module 198 adds `DistributedSystemsFullSuite.lock_handover`: checked adoption, conditional round-zero agreement and justified finite local lock replacements.

Module 199 adds `DistributedSystemsFullSuite.handover_induction`: conditional all-round agreement and registered local execution refinement.

Release v0.7.9 registers `DistributedSystemsFullSuite.epoch_transition_master`,
`QuantumPhysicsFullSuite.hctk_scalar`, and `DistributedSystemsFullSuite.header_chain_auth`.
Their conditional formal scopes are described in the new module cards.

Release v0.7.10 adds `CryptoFullSuite.ipa_forking` and preserves the refined
`QuantumPhysicsFullSuite.hctk_scalar` contract. The new finite acquisition
result retains response availability and cryptographic security as external obligations.

Release v0.7.11 adds `CryptoFullSuite.ipa_probability`: finite distinct-square
fork probabilities and heavy-prefix bounds, with explicit valid-child premises
for extractor composition. General forking and ROM security remain open.

Release v0.7.12 adds `CryptoFullSuite.ipa_tree_probability` and
`CryptoFullSuite.ipa_bounded_retry`: complete-tree conditional probability,
first-success extraction and finite expected attempt count. No ROM/PPT claim.

Release v0.7.13 adds `CryptoFullSuite.ipa_product_tapes` and
`CryptoFullSuite.ipa_recursive_generator`: concrete independent retry tapes,
recursive checked child generation and finite conditional tree probability.
Source availability, ROM and runtime claims remain outside the proved guarantees.

Release v0.7.14 adds `CryptoFullSuite.ipa_node_retry`: independent local retries
at every recursive IPA node, exact finite probabilities and conditional lower
bounds. Strict actual amplification requires an actual attempt rate in (0,1).

Release v0.7.15 adds `CryptoFullSuite.ipa_partial_cache`: fixed-fork partial-cache
context safety, scheduled child-call dominance and independent exact probabilities.

Release v0.7.16 adds `CryptoFullSuite.ipa_public_scalar`: two supplied outer trees
bind dot(a,b)=c or yield an explicit original-generator relation; obtaining the pair remains external.

Release v0.7.17 adds `CryptoFullSuite.ipa_pedersen_consistency`: a supplied
Pedersen fork and two IPA trees are checked at one extracted scalar, yielding
a joint witness or an extended-generator relation. No single-transcript hidden-c
verifier or full ZK is claimed.

Release v0.7.18 adds `CryptoFullSuite.hidden_scalar_protocol`: full-vector
interactive hidden-inner-product verification, three-point witness-or-relation
extraction, and exact honest-verifier simulation under bijective blinding.
IPA compression, adversarial fork acquisition, ROM and PPT remain outside scope.

Release v0.7.19 adds `CryptoFullSuite.hidden_scalar_compression`: complete
single-path IPA compression, causal independent execution, exact HVZK under
bijective blinding, and witness-or-relation extraction from six supplied trees.
Adversarial fork acquisition, ROM and polynomial-time guarantees remain open.

Release v0.7.20 adds `CryptoFullSuite.fork_acquisition`: snapshot-indexed nested
acquisition with model-relative provenance and witness-or-relation extraction.
Exact Q/R costs apply to Clean runs; arbitrary runs retain actual logs and schedule
bounds. Conditional probability premises remain explicit; no ROM or PPT claim.

Release v0.7.21 adds `CryptoFullSuite.fork_progress`: conditional quota probability
bounds for retained branches, including retries, with direct snapshot adapters
and provenance/extraction composition. No independence or global-density inference.

Release v0.7.22 adds `CryptoFullSuite.fork_schedule`: independent finite full-probe
schedules derive conditional progress rates max(0,d-j beta). Local success density
and per-class mass bounds remain explicit; snapshot acquisition and extraction are reused.

Release v0.7.23 adds CryptoFullSuite.fork_local_density and fork_recursive_quota.
Exact child-law averaging and bottom-up quota4/2/3 bounds use actual snapshot
acquisition and extraction. Concrete finite iid microseed laws have common shape
and budget per depth, with snapshot-dependent call decoding and proven key masses.
No global acceptance inference, external-process refinement, ROM or runtime claim.

Release v0.7.24 adds CryptoFullSuite.single_path.
Actual causal execution is equivalent to compressedVerify with exact reachable
snapshots and finite microseed prefix decomposition. Complete rejected transcripts
remain produced with accepted=false; aborts and malformed packets produce none.
Heavy-prefix bounds do not yet imply recursive quota completion.

Release v0.7.25 adds CryptoFullSuite.threshold_quota.
Guarded local single-path rates and profile monotonicity support recursive
threshold transfer into actual fork acquisition. Acceptance above the root
threshold and a positive computed bound imply witness-or-generator-relation
extraction for the fixed-tape finite microseed plan.

Release v0.7.26 adds CryptoFullSuite.tape_average and
DistributedSystemsFullSuite.external_actuator. Finite tape averaging retains
acceptance guards and dependent plan seed laws. The actuator model proves
at-most-once software dispatch under its sequential durable-history transitions;
physical effects and concrete implementation refinement are not established.

Release v0.7.27 adds CryptoFullSuite.heavy_tape and
DistributedSystemsFullSuite.actuator_arbitration. Weighted heavy-tape bounds
retain separate positive quota margins. Serialized arbitration preserves receipts
and grant history; physical effects and implementation refinement are not established.

Release v0.7.28 adds CryptoFullSuite.quota_margin: decidable recursive
arithmetic certificates, an exact finite minimum and positive-mass extraction
under separate acceptance and tape-weight hypotheses.

Release v0.7.29 adds CryptoFullSuite.quota_product: exact diagonals,
budget monotonicity, explicit margin powers and budget-sensitive tape minima.

Release v0.7.30 adds CryptoFullSuite.quota_deficit: submultiplicative deficits,
analytical geometric block bounds and explicit multiblock tape budgets.

Release v0.7.31 adds CryptoFullSuite.quota_budget: minimal geometric block budgets,
root deficit targets and weighted outside-set error bounds.

Release v0.7.32 adds CryptoFullSuite.quota_minimum: exact finite reference-quota budget search,
global minimality on success and bounded-window failure.

Release v0.7.33 adds CryptoFullSuite.quota_tabular: materialized quota rows,
exact scalar, deficit and bounded-search equivalence for arbitrary rational profiles.

Release v0.7.34 adds CryptoFullSuite.quota_streaming: streaming search with reusable rows,
unconditional Option equality with the reference bounded search.

Release v0.7.35 adds CryptoFullSuite.quota_cost: instrumented streaming search,
exact structural counters and unconditional Option equality.

Release v0.7.36 adds CryptoFullSuite.quota_comparison: tabular/streaming cost comparison,
exact triangular counters and unconditional Option equality.

Release v0.7.37 adds CryptoFullSuite.quota_fast: fast boundary branches,
exact branch-sensitive counters and unconditional Option equality.

Release v0.7.38 adds CryptoFullSuite.quota_resumable: certified resumable search,
retained-row/prefix invariants and conditional continuation equivalence.

Release v0.7.39 adds CryptoFullSuite.quota_resume_cost: instrumented resumption,
full retained-result equality and exact four-counter additivity for nondecreasing caps.

Release v0.7.40 adds CryptoFullSuite.quota_chain: finite quota chains,
full state and four-counter equality under List.IsChain (<=) (cap0::caps).

Release v0.7.41 adds CryptoFullSuite.quota_fast_start: fast successful quota starts,
full result equality and exact branch-specific structural counts.

Release v0.7.42 adds CryptoFullSuite.quota_fast_chain: fast-start quota chains,
full state/cost pair equality under nondecreasing caps.

Release v0.7.43 adds CryptoFullSuite.quota_snapshot: typed cursor snapshots,
checked restoration, exact round trip and safe continuation.

Release v0.7.44 adds quota_codec, quota_canonical_wire and quota_profile: bounded canonical bytes, strict structured representations and independently checked finite profile transfer.

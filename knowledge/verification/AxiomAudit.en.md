---
id: AxiomAudit
language: en
section: verification
source: Verification/AxiomAudit.lean
source_sha256: dfb301a46baa5100597f1074714dd6371f65960a7fee4011a4af14bc660b30b1
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

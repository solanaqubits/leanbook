---
id: MasterSuiteComponents
language: en
section: verification
source: Verification/MasterSuiteComponents.lean
source_sha256: ec3b2d818a1e8ba9fe6fee1b90a037604a9bc516d1dc3b0685a9c5a28448b0df
novelty: not-assessed
status: reviewed
---

# MasterSuiteComponents

[Section](README.md) · [Lean](../../Verification/MasterSuiteComponents.lean)

## Reusable package declarations

This module holds the existing package structures, proof constructors, and compatibility projections extracted from `MasterSuite.lean`. Their namespace remains `MasterSuite`; moving the source location does not rename the declarations. The extracted declaration block preserves the prior definitions and proof bodies, including inherited fields, Lamzouri's integral and unique-minimum results, and compatibility projections for existing components.

The top-level package types are `FinslerFullSuite`, `LamzouriFullSuite`, `CollatzFullSuite`, `CryptoFullSuite`, `QuantumPhysicsFullSuite`, `HopfFullSuite`, `ProofDAGFullSuite`, `FinanceRiskFullSuite`, `DistributedSystemsFullSuite`, `RiemannFullSuite`, and `PhotonicsInterposerFullSuite`. Supporting `FinslerFormalSuite` and `FinanceDeFiFullSuite` remain available. Each package has its existing constructor theorem, such as `crypto_full_master_suite`, `quantum_physics_full_master_suite`, and `distributed_systems_full_master_suite`.

Universe declarations are retained. In particular, the crypto package carries the AIR and FRI universe parameters, the distributed package carries the Raft universe parameters, and the Hopf package quantifies over its original ambient type universe. These abstractions have not been replaced with finite examples or fixed universe instances.

## Dependency purpose

The module imports the original 99 domain modules and the operational Chandy–Lamport and exact QPE modules. DistributedSystemsFullSuite now includes chandy_lamport; aggregates referring to this package inherit the added field. [`MasterHundredRegistry`](../11_meta_registry/MasterHundredRegistry.md) imports these components to assemble the milestone proposition, and the central [`MasterSuite`](MasterSuite.en.md) can import that milestone. Components do not import either registry, avoiding a cycle. The central registry declaration itself is not defined in this file.

The split is organizational. It introduces no new domain result and does not enlarge the meaning of any imported guarantee. A suite bundles selected propositions; it does not certify every declaration in its imports or complete coverage of every subject block. Counts of imports and source files are external repository checks, not theorems of the component packages.

The domain limitations remain in force. For example, `QuantumPhysicsFullSuite.beam_splitter` is a real orthogonal finite two-mode/two-boson model, not general complex unitarity. `CryptoFullSuite.forking_lemma` concerns finite matrix counting and scalar extraction. `DistributedSystemsFullSuite.marzullo_algorithm` concerns a threshold envelope with explicit interval assumptions. Aggregating these fields supplies no additional physical, cryptographic, or protocol guarantee.

## Verification

See the [current validation record](../VERIFICATION.en.md). The operational snapshot field is constructed by `DistributedChandyLamportSnapshot.chandy_lamport_master_suite`; it proves the two-process safety and completed-channel guarantees described in its [scope card](../09_distributed_systems/DistributedChandyLamportSnapshot.md). The historical registry's import manifest is unchanged, but its distributed package type includes this added field.

QuantumPhysicsFullSuite now includes phase_estimation, constructed by QuantumPhaseEstimation.quantum_phase_estimation_master_suite. It preserves the exact two-bit phase and eigenstate hypotheses; existing aggregates referencing the quantum package inherit the field.

`QuantumPhysicsFullSuite.grover_multiple_targets` adds exact N=4 subset dynamics, norm preservation, the proper-subset invariant plane and both rank-one reflection counterexamples.

`QuantumPhysicsFullSuite.deutsch_jozsa_general` adds the general Hadamard and XOR-ancilla circuit, promise separation, edge cases and one-qubit compatibility.

`DistributedSystemsFullSuite.raft_commit_application` adds operational commit-index provenance and deterministic local application. Global State Machine Safety is not claimed by this extension.

`DistributedSystemsFullSuite.two_phase_commit_timeout` adds reachable operational agreement, pre-vote abort safety, prepared-view indistinguishability and the conditional stopped-coordinator blocking equivalence. The legacy `two_pc` field is preserved.

`DistributedSystemsFullSuite.three_phase_commit` includes operational two-participant agreement, finite completion paths and conditional weak-fair completion. The accurate epoch-view service remains an explicit environment contract.

DistributedSystemsFullSuite.chandy_misra_haas adds inductive probe provenance and soundness for a fixed AND wait graph, finite detection paths and conditional progress under payload delivery fairness. Fresh-epoch reset is an external contract; arbitrary dynamic WFG soundness is explicitly refuted for the naive send-time-only extension. See the [CMH scope card](../09_distributed_systems/DistributedChandyMisraHaasDeadlock.md).

QuantumPhysicsFullSuite includes grover_arbitrary_phase, preserving the single-target C^4 scope: arbitrary phases preserve a complex plane, exact one-step success has cos(phi)=-1, and the canonical bridge includes a global minus sign.

`QuantumPhysicsFullSuite.simon` adds the complex two-register circuit, exact Simon distribution and rank-conditional binary period recovery. Existing fields are preserved.

`QuantumPhysicsFullSuite.phase_estimation_general` adds general controlled-power QPE, unitary Fourier transforms, exact dyadic recovery and the nearest-sample 4/π² probability bound. A normalized eigenstate is supplied. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumPhaseEstimationGeneral.md).

`QuantumPhysicsFullSuite.shor_order_finding` derives the padded modular-multiplication spectrum and the QPE marginal on |1⟩. The component bound is 4/π²; its guaranteed contribution to the mixture is 4/(rπ²). Order recovery and factorization are not claimed. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumShorOrderFindingCore.md).

`DistributedSystemsFullSuite.suzuki_kasami` proves reachable token conservation and mutual exclusion. Eventual service requires ReliableDelivery, WeakFairness and FiniteCS. A reachable counterexample refutes LN ≤ RN at the holder. [Scope and serialization](../09_distributed_systems/DistributedSuzukiKasamiMutex.md).

`QuantumPhysicsFullSuite.shor_continued_fractions` proves finite executable candidates and conditional recovery under the strict Legendre bound. Euclidean stages are bounded separately from bit complexity. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumShorContinuedFractions.md).

`QuantumPhysicsFullSuite.shor_order_recovery` proves conditional recovery from certified divisors, the spectral GCD criterion and a counterexample to taking all candidate denominators. [Scope and assumptions](../03_quantum_physics_and_optics/QuantumShorOrderRecoveryGCD.md).

`DistributedSystemsFullSuite.raymond_tree` includes reachable token conservation, effective holder routing, conditional starvation freedom and exact isolated traffic. [Contract](../09_distributed_systems/DistributedRaymondTreeMutex.md).

`QuantumPhysicsFullSuite.naimark` adds finite POVM dilation, Born-trace preservation, a unitary extension with a fixed pure ancilla and Lueders reduction. POVM effects do not uniquely specify state updates. [Contract](../03_quantum_physics_and_optics/QuantumPOVMNaimarkDilation.md).

The `QuantumPhysicsFullSuite.no_cloning_unitary` field includes the exact unitary
no-cloning suite, with phase-invariant density overlap constraints and BB84 obstruction.

`DistributedSystemsFullSuite.coordinated_attack` adds finite-horizon coordinated
attack impossibility, with delivery-removal indistinguishability derived from
local transitions. Agreement and ValidityZero force retreat, contradicting
ReliableSuccess. [Contract](../09_distributed_systems/DistributedCoordinatedAttackImpossibility.md).

`CryptoFullSuite.musig_group` adds finite cyclic-group Schnorr aggregation,
composition of accepted partial responses and a naive rogue-key witness.
[Contract](../04_cryptography/CryptoSchnorrMultiSignaturesMuSigGroup.md).

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

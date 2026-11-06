# Quantum v4.23 — independent stages and post-analyzer coupling

Local scoped/gamma candidate on `2f56a1a3d80a95a01277fcfaa2693e477c4f5f41`
(v4.22), branch `quantum-postmeasurement-v423`. Published Leanbook `v1.0.0`
remains unchanged. Toolchain and pinned Mathlib are unchanged.

[Exact inventory](quantum-v4.23-inventory.json) ·
[Verification record](quantum-v4.23-verification.json)

## Independent environment stages

`QuantumTensorStageEnvironment` defines `tensorGate`, `tensorStage`, `stageStep`
and `tensorStages`. A list of pairs `Stage n × Stage e` allows each step to have
its own environment unitary, CPTP channel and finite Kraus-label type. The theorem
`traceEnvironment_run_tensorStages` eliminates this independent environment
activity under partial trace for every joint matrix, without a PSD or product
premise. `tensorStages_outcome_marginal_reduction` lifts the result to all five
outcomes and arbitrary readout. The uniform-environment corollary matches the
proposed `ss.map` interface.

`tensorStage_identity_step_eq_extendStage` and `tensorStages_identity_run` compare
actions with v4.22. They do not equate `labels × Unit` and `labels` as Stage data.
Regression fixtures include heterogeneous label types, arbitrary environment
unitaries and nonunital `reset 0`, whose image of identity has entry 2.

## Interaction that the instrument cannot distinguish

`QuantumPostBSMEnvironment.postBSMCnotBE` is a CNOT from B to E. It is appended
immediately before computational BC readout, after the preceding chronological
run. `postBSMCnotBE_not_kronecker_product` excludes every factorization
`A ⊗ B`, even without requiring either proposed factor to be unitary.

The cancellation lemma uses `computationalReduction m`, or its corrected operator
`correction r * computationalReduction m`. It deliberately does not use
`branchOperator`, which already includes the Bell analyzer. Within a fixed
computational branch both sides have the same measured B value. The environment
index is permuted equally on both sides; AD coherences remain intact.

`post_interaction_outcome_invariant` proves equality of all five reduced outcomes
for arbitrary Readout, arbitrary joint matrix, and **any preceding joint stage
list**. This does not make arbitrary preceding interactions marginally reducible.
The specialized `postBSMCnotBE_preserves_all_reducedJointOutcomes` derives
marginal dependence for an extended system-only Bell analyzer followed by this
nonfactorizing interaction.

A normalized PSD pure probe is specified at this measurement cut. Its joint
matrix changes under the CNOT. The transformed matrix is the outer product of
`coupledKet`, and `coupledKet_not_product` excludes a system/environment vector
factorization. This is a pure-state obstruction; no general mixed-state
separability predicate is introduced.

## Boundaries and regression history

The two modules contain 30 named theorem declarations (9 and 21), including
helpers and two registry suites. The inventory exports 45 named source
declarations including definitions and suite structures. These are code metrics,
not counts of independent scientific results.

The original external-qubit CNOT A-to-E claim is false and is not restored.
Its optional separate coherence-counterexample theorem is not part of this
candidate. A single changed output on one input would not by itself establish
the absence of every marginal-only map. The earlier v4.21/v4.22 witnesses retain
their precise two-input obstructions and placement constraints.

No full classification of interactions, adaptive process tensor, or hardware
claim is made. Independent-environment reduction is sufficient, not necessary.
Initial correlations may persist in the full joint state.

Validation is scoped/gamma. The exact report records strict elaboration,
incremental integration build, imported axiom closure, independent compiled
project audit and targeted container tests. No fresh full `verify-all`, full
unittest discovery, clean build or remote CI run is claimed. The last full
validation checkpoint remains v4.21 with its documented multi-run test history;
v4.22 and v4.23 add bounded evidence only.

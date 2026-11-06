# Quantum v4.22: marginal reduction and probability obstruction

Local additive candidate on `127a55b885f1cb6ad67132d6a0f3d4d8f56ff607`
(Quantum v4.21). Published Leanbook v1.0.0 remains unchanged.
[Theorem inventory](quantum-v4.22-inventory.json) ·
[Verification record](quantum-v4.22-verification.json).

## Sufficient reduction conditions

`QuantumDecoupledEnvironment.extendStages` extends each system gate and noise
channel with the identity on a finite environment. Its five-outcome theorem holds
for every joint matrix, arbitrary system stage lists, and arbitrary Readout.
It needs no product input, PSD assumption, or ideal-analyzer hypothesis.
The proof commutes partial trace with chronological `run`, then reconstructs
micro/reject branches from the resulting matrix. In particular, it does not rely
on the vacuous reject branch of perfect readout.

A separate `tensorCPTP` construction treats independent system and environment
channels. `traceEnvironment_tensorCPTP` uses the environment channel's trace
preservation. Unitality is not required; the regression uses a reset channel that
maps the identity to twice a rank-one projector. Kraus factors are independent:
this does not cover shared correlated noise labels or controlled interactions.
These are sufficient conditions, not a necessary-and-sufficient classification.
Correlations can remain in the joint state before the environment is traced out.

## Fixed-interaction probability witness

`QuantumCorrelatedProbabilityWitness` uses GHZ and its B-bit flip. Two equal-weight
mixtures correlated with orthogonal environment states have the same system AND
environment marginals, are PSD, and have trace one. The unchanged v4.21
`witnessStages` applies the environment-controlled flip BEFORE the Bell analyzer.

With perfect readout, the complete complex branch traces, ordered as
Phi+, Phi-, Psi+, Psi-, are `(1/2, 1/2, 0, 0)` and `(0, 0, 1/2, 1/2)`.
Thus the Phi+ probability is not a function of the system marginal for this fixed
configuration on all physical joint inputs. PSD and zero trace also prove that
the second input's Phi+ branch is the zero matrix. This is an actual probability
shift, unlike the equal-probability output-state witness of v4.21.

## Verification scope

This is a bounded additive change: existing theorem statements and primitive
definitions are unchanged. Registry fields are added; verifier, toolchain and
dependency revisions are unchanged. Strict elaboration and a transitive axiom audit
cover both new modules; the registry and root builds cover their integration.
Targeted live tests include v4.20, v4.21 and the new v4.22 fixtures, in a qualified
container with 12 GiB memory, 4 CPUs, swap disabled and pinned SQLite/libsodium.
The module audit passed on 4,614 declarations across 53 imported sources; the
independent auditor passed on 42,804 compiled project declarations. Both found only
`propext`, `Classical.choice`, and `Quot.sound`, with no violations. The incremental
build passed (4124 jobs, five freshly built targets at the final step). All seven
targeted tests passed with zero failures or skips. The synchronization evidence
records source hashes and the 38 actual exports (including 30 named theorems). Cached
builds are distinguished from re-elaboration. No fresh whole-library verify-all
or complete unittest discovery is claimed for v4.22.

## Boundaries

One finite-dimensional cycle, not adaptive process tensors. No universal
classification of interactions, general assignment-map theorem, hardware
characterization or novelty assessment. The witness environment is a qubit;
the reduction theorems allow arbitrary finite dimensions.

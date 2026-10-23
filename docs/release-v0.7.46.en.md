# Release v0.7.46 — provenance, replay and conditional models

This cumulative synchronization includes nine new modules relative to v0.7.45:

| Module | Scope |
|---|---|
| DigitalProvenanceVerificationContract | Exact acceptance relative to explicit crypto callbacks, independently supplied context and key/time policy |
| DigitalProvenanceReplayContract | Raw-byte challenge identity, refusal preservation and inductive sequential replay rejection |
| PrometheusChannelAndInjectorAudit | Conditional finite-channel and injector bookkeeping |
| PrometheusDecoderQueue | Conditional single-server queue and serialization algebra |
| PrometheusFiniteBlockAudit | Constructive finite-block conditional reliability bounds |
| PrometheusPipelinedQueue | Conditional pipelined queue and finite-buffer obligations |
| PrometheusMetrologyJitter | Conditional phase response and timestamp covariance |
| PrometheusNQKDAudit | Explicit ideal-qubit interception/noise model and counterexamples to universal disturbance |
| PrometheusTAKLAudit | Phase invariance and conditional density/ring-model bounds |

The registry contains 259 direct MasterSuite imports and 303 Lean sources including
Verification.lean. Test/tool Lean files are separate from this source count.
Proof sources are exported byte-for-byte from one pinned development snapshot.
The publication report records that pin, final commit/tag identities and actual
public validation results. English explanatory cards and regression tests accompany
the new modules; private numerical studies and knowledge archives are not exported.

Verification includes strict Lake builds, the explicit qutrit Spec target, all public
unittests with live checks and a transitive axiom audit. Only propext,
Classical.choice and Quot.sound are permitted. Validation scope is selected from
the actual change impact; historical development checks in cards are not substitutes
for this independent public-tree control.

Provenance acceptance is relative to supplied functions, not an implementation or
security proof of SHA-256/Ed25519 or trusted key/time infrastructure. Sequential
replay rejection excludes rollback, concurrent stale-state readers and storage loss.
Authorization remains blocked in the modeled result. Recovery and persistence
require separate contracts. The conditional physics/queue results do not establish
physical apparatus qualification, universal deadlines, composable QKD security or
a new weak-interaction mechanism.

Lake remains 0.7.1. The designated public beta baseline remains v0.7.1 at
2419489245019fb16e32ffac641b9f88eea94126; this release assigns no new beta baseline tag.

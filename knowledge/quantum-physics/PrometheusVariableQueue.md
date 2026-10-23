---
id: PrometheusVariableQueue
language: en
section: quantum-physics
source: Verification/PrometheusVariableQueue.lean
novelty: not-assessed
status: reviewed
source_sha256: d3f329fe3c01037188342f923e49deea58e6290c1ece215d6f176158155757fc
---

# PrometheusVariableQueue

[Section](README.md) · [Lean](../../Verification/PrometheusVariableQueue.lean)

The module extends epsilon250/253 with an explicit complete-before-admit
counting transition. Capacity counts all resident jobs, including service.
Induction proves offered = completed + occupancy + rejected and occupancy ≤ capacity.
Cumulative envelopes offered(n) ≥ a n and completed(n) ≤ s n + b imply
occupancy + rejected ≥ (a−s)n−b. Positive excess forces unbounded losses under
finite capacity, or unbounded occupancy when losses are zero.

Initially idle constant-service cyclic FIFO lanes have zero waiting exactly when
service ≤ P·dt, including equality. Above the threshold waiting is unbounded.
These are conditional deterministic results, not stochastic stability or a proof
of a measured trace's sustainable rate. Historical medians are not WCET premises.

Entry points: `run_balanced`, `run_capacity`, `cumulative_excess`,
`finite_capacity_unbounded_loss`, `no_loss_unbounded_occupancy`, `cyclic_threshold`.
Registry field: `QuantumPhysicsFullSuite.prometheus_variable_queue`.
Direct dependency: `Verification.PrometheusPipelinedQueue`.
Strict development build and 17 queue examples passed. Integration performs the
final scoped axiom and registry checks; see the external scoped evidence ledger.
No physical device, runtime scheduler refinement or hardware authorization follows.
Novelty has not been assessed.

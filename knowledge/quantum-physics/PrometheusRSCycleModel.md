---
id: PrometheusRSCycleModel
language: en
section: quantum-physics
source: Verification/PrometheusRSCycleModel.lean
novelty: not-assessed
status: reviewed
source_sha256: 4f2cf41c9c2cf25fa00fa120dc1f8c49b184ed0bcff83350cf3e220c53e7b61a
---

# Deterministic RS decoder control schedule

[Section](README.md) · [Lean](../../Verification/PrometheusRSCycleModel.lean)

The concrete program has2959 instructions plus one terminal clock, total2960. Each step applies an arbitrary total datapath kernel to one instruction, then Done(status) is produced on the empty list. Induction proves the final result and absence of early termination; exact execution time is independent of input data. The listed stage budgets match the Python wide-macrocycle model. Conditional250/500MHz unstalled execution gives11.84/5.92microseconds. Parallel GF operators, reduction trees and inverse ROM access are explicit resource hypotheses, not synthesized hardware.

No universal RS algebraic correctness, Python/RTL refinement, achieved frequency, no-stall implementation or hardware WCET. Repetition voting,9600-slot serialization, queueing and flight are excluded. Success does not establish original-message identity; outside the radius another valid packet may be accepted.

Historical private checks are reported separately. Fresh public-tree verification is recorded in the [scoped receipt](../../docs/prometheus-lean-checks.json). This is not a new full beta checkpoint. Physical feasibility, hardware WCET, certified positive SKR and the Third Obligation remain OPEN.

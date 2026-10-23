---
id: PrometheusNQKDFiniteKey
language: en
section: quantum-physics
source: Verification/PrometheusNQKDFiniteKey.lean
novelty: not-assessed
status: reviewed
source_sha256: 455664c4f99b94810fe540d09894a4f3ff3ee898a9fd56fbd86a657ae21f8e63
---

# Conditional finite-key bookkeeping and abort guards

[Section](README.md) · [Lean](../../Verification/PrometheusNQKDFiniteKey.lean)

Proves the exact integer threshold, rate condition, explicit abort guards, scalar sampling-slack algebra and the integer extraction residual bound. Serfling sampling and the quantum LHL/entropy bridge remain explicit external premises. No general sampling theorem, quantum reduction, historical-protocol security or certified positive SKR is claimed. Authentication key consumption is separate from public leakage.

Counterexample: a positive half-bit budget gives zero output. The ordinary binary entropy at q=1 is zero, hence the explicit phase guard is necessary. Historical public leakage301+64+1=366; the128-bit authentication key cost is not another public raw-key leak.

Historical private checks are reported separately. Fresh public-tree verification is recorded in the [scoped receipt](../../docs/prometheus-lean-checks.json). This is not a new full beta checkpoint. Physical feasibility, hardware WCET, certified positive SKR and the Third Obligation remain OPEN.

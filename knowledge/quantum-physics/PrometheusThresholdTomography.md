---
id: PrometheusThresholdTomography
language: en
section: quantum-physics
source: Verification/PrometheusThresholdTomography.lean
novelty: not-assessed
status: reviewed
source_sha256: e421e99e6e09120d42ba6dabb84b0dc399cf666377045195da3f94638d5cf970
---

# Threshold information and observation rank

[Section](README.md) · [Lean](../../Verification/PrometheusThresholdTomography.lean)

Proves normalization of a finite observation kernel and an exact atomic threshold-channel MI: one bit at threshold ≤1, zero otherwise. Midpoint counterexamples disprove both convexity and concavity. This does not establish the shape of a different mixture objective or global optimality of a numerical grid.

For a linear sensitivity matrix A, proves equality of ranks and kernels of A and AᵀA, and injectivity iff the Gram kernel vanishes. Arbitrarily many energy rows do not remove duplicate columns: (1,-1) is an explicit hidden direction and rank<2. Also proves the exact source-flux/efficiency product ambiguity and the observation-count rank bound.

This is first-order algebra. Oscillation derivatives and computed numerical ranks are not Lean-certified. A zero Jacobian alone does not disprove nonlinear identifiability. No physical tomography, OAM/MSW lensing or hardware implementation is proved.

Key declarations: `atomic_information`, `atomic_not_concave`, `atomic_not_convex`, `gram_rank`, `identifiable_iff_gram_kernel`, `duplicate_rank_lt_two`, `flux_efficiency_gauge`.

Historical private checks are reported separately. Fresh public-tree verification is recorded in the [scoped receipt](../../docs/prometheus-lean-checks.json). This is not a new full beta checkpoint. Physical feasibility, hardware WCET, certified positive SKR and the Third Obligation remain OPEN.

---
id: PrometheusLifetimeIdentifiability
language: en
section: quantum-physics
source: Verification/PrometheusLifetimeIdentifiability.lean
novelty: not-assessed
status: reviewed
source_sha256: 43aab6100cf254c6653ee9d5ae6dcff49fd17805a1cb9fbab42c256e2c634681
---

# Two beta bins and a terminal survivor count

[Section](README.md) · [Lean](../../Verification/PrometheusLifetimeIdentifiability.lean)

N is the mean of a Poisson initial ensemble. Two adjacent bins [0,h),[h,2h), terminal emptying at2h. For calibrated positive efficiencies, positive h,b,N, nonnegative loss and known nonnegative backgrounds, actual mean derivatives, determinant, positive definiteness and positive determinant of J-transpose diag(1/mu) J are proved. Exact recovery from means establishes structural identification. Zero beta efficiency is singular; rescaling beta and inverse efficiency with constant total loss preserves all three means. Poisson thinning and the expected score-square identity are model assumptions, not Mathlib probability theorems here. The log likelihood is defined and the displayed Jacobian is differentiated.

No arbitrary-bin-layout, fixed-population or unknown-calibration guarantee. No attained0.1s accuracy or finite-sample coverage certificate.

Historical private checks are reported separately. Fresh public-tree verification is recorded in the [scoped receipt](../../docs/prometheus-lean-checks.json). This is not a new full beta checkpoint. Physical feasibility, hardware WCET, certified positive SKR and the Third Obligation remain OPEN.

---
id: PrometheusJitterWindow
language: en
section: quantum-physics
source: Verification/PrometheusJitterWindow.lean
novelty: not-assessed
status: reviewed
source_sha256: 4bb1e74579ba5be44f060e7ba9fa3ef6bdd28222f88671b435235cf64037905a
---

# Relative jitter and coincidence acceptance

[Section](README.md) · [Lean](../../Verification/PrometheusJitterWindow.lean)

Identical common-mode coupling cancels pointwise without independence from C. L2 channel noise gives variance of difference Va+Vr-2Cov and strict reduction against the fixed marginal sum for positive covariance. Chebyshev is centered; the biased gate uses w>|mean| and denominator (w-|mean|)^2. An explicit joint Gaussian law yields a Gaussian difference law. Standardization and the measure-defined CDF give exact gate acceptance with a nonzero mean allowed. Zero variance uses a Dirac law.

No measured physical detector traces or distribution inferred from variance alone. Student-t3 is a separate numerical model; t1 lacks finite variance. No end-to-end PER or hardware calibration.

Historical private checks are reported separately. Fresh public-tree verification is recorded in the [scoped receipt](../../docs/prometheus-lean-checks.json). This is not a new full beta checkpoint. Physical feasibility, hardware WCET, certified positive SKR and the Third Obligation remain OPEN.

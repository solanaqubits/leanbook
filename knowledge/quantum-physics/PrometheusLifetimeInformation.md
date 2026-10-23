---
id: PrometheusLifetimeInformation
language: en
section: quantum-physics
source: Verification/PrometheusLifetimeInformation.lean
novelty: not-assessed
status: reviewed
source_sha256: 8995babe9ca365e602c24889f7e21227475f6324950ddb3f211a135de5c09c72
---

# PrometheusLifetimeInformation

[Section](README.md) · [Lean](../../Verification/PrometheusLifetimeInformation.lean)

Source energy determines neither realized photoelectron count nor timing
precision. Expected photoelectrons are a conditional product of source energy,
geometry, deposition, photons per joule, transport and PDE. Zero acceptance and
zero-count timestamp counterexamples preserve the positive neutron source energy.
Beta detection probability is a separate calibration quantity.

For a normalized finite law, mean(score)=0, cov(error,score)=1 and positive score
variance imply Var(error) ≥ 1/Var(score). Zero information cannot satisfy the unit
covariance identity. A scalar nuisance projection gives the corresponding bound
under an explicit estimator–nuisance orthogonality assumption, and its variance
is the scalar Schur-complement information. It cannot exceed the original score
variance. Parametric regularity, unbiasedness, Poisson MLE precision and interval
coverage are not inferred from this finite-law algebra.

Disappearance rate = 1/betaLifetime + lossRate is nonidentifiable when losses are
unknown: (1,0) and (2,1/2) agree. An independently known identical loss rate restores
identifiability for positive lifetimes. An effective lifetime is not the beta lifetime.

Entry points: `positive_energy_without_timestamp`, `score_information_bound`,
`zero_information_no_unit_identity`, `nuisance_information_bound`,
`residual_information`, `known_loss_identifiable`.
Registry: `QuantumPhysicsFullSuite.prometheus_lifetime_information`.
Dependency: `Verification.PrometheusMetrologyJitter`.
Strict development build and 16 metrology examples passed; integration performs the
final scoped axiom and registry checks, recorded externally. No full-beta audit,
physical calibration or authorization change is asserted. Novelty not assessed.

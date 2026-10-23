---
id: PrometheusMetrologyJitter
language: en
section: quantum-physics
source: Verification/PrometheusMetrologyJitter.lean
novelty: not-assessed
status: reviewed
source_sha256: ceba223a1d77a88058f4705ab646d56b89a10f2320ab37227d6afeff3f8d9404
---

# Conditional matter-action and timing covariance

[Section](README.md) · [Lean](../../Verification/PrometheusMetrologyJitter.lean)

Epsilon254, quantum-physics/prometheus-pipeline-metrology. This separates a
continuous scalar matter contribution, finite quadrature covariance, and a
conditionally calibrated timestamp estimator. None is a physical neutrino link
qualification or a proof of phase-driven beam pointing/arrival delay.

## Continuous quantity and finite covariance

electronDensity(x)=density(x)*NA*Ye(x). The scalar perturbation is
phi=(kappa*NA)*integral_0^L density(x)*deltaYe(x) dx. It is a matter-potential
action contribution, not the full flavor propagator for a generally noncommuting
spatial Hamiltonian. Consistent units, density/composition and coupling are inputs.
With L>=0,rhoMax>=0, integrable density*deltaYe and absolute profile bounds
|density|<=rhoMax, |deltaYe|<=epsilon on the interval, Lean proves
|phi|<=|kappa*NA|rhoMax*epsilon*L. Additivity and density scaling are proved;
composition uncertainty alone does not determine this bound.

FiniteLaw supplies nonnegative normalized masses on a finite outcome space.
mean, centered covariance and variance are defined as actual weighted sums;
variance is nonnegative. For each integrable profile in this finite space,
Var(phi)=(kappa*NA)^2 Var(integral density*deltaYe). This connects the continuous
integral to variance exactly; no covariance double-integral/Fubini theorem is
claimed. The numerical Gaussian ensemble is not this finite-law formalization.

Separately, quadrature weights wi=kappa*NA*width_i*density_i give
Var(sum_i wi*deltaYe_i)=sum_ij wi*wj*Cov(deltaYe_i,deltaYe_j).
Off-diagonal covariances are included. A diagonal sum follows only from explicit
pairwise zero covariance. Quadrature approximation accuracy/convergence to the
continuous integral is not established. Tests show a shared perturbation with
weights2 and3 has variance25, not the diagonal-only13.

## Calibration, wrapping and photon observations

CalibratedBound(response,g) explicitly requires
|response(x)-response(y)|<=g*|x-y|. For g>=0 this propagates a phase error bound
into a response error bound, including the continuous bound relative to phase0.
An affine response offset+gain*x satisfies this condition with |gain|.
Var(gain*phase)=gain^2 Var(phase); zero gain cannot identify different phases.
No such calibration gain is derived from MSW physics.

PhaseEquivalent(T,x,y) means x-y=k*T for an integer k. Aliased phases x and x+T
are distinct for T>0. Equality of representatives follows only with the additional
branch condition |x-y|<T. This is a scalar unwrap theorem, not a measured phase
estimator or an assertion that a physical observable reveals the phase.

For fixed positive detected photon count M, photonAverage is the sample mean.
Equal individual variance V and pairwise zero covariance imply variance V/M.
If shared onset noise has zero covariance with every photon contribution, adding
it gives V/M+Var(shared). The shared term is not divided by M. Subtracting the
specified response mean removes the stipulated bias; calibration correctness
remains an assumption. sampleTimestamp returns none for M=0, not zero or a
fabricated estimate. General variance identities retain covariance terms:
Var(X-Y)=Var(X)+Var(Y)-2Cov(X,Y). The same additive common mode cancels exactly
in X+C-(Y+C), without an independence premise. Tests include independent and
fully correlated photon examples. There is no Poisson-mixture proof, physical
scintillation kernel, SiPM hardware refinement, or photon-production yield law.

The inherited exact neutron kinetic energy1.17759982599e-6J is reused only as an
energy identity. It is not instantaneous optical emission, deposited light energy,
or electrical output.

## Verification and scope

Standard verify passed: 252 declarations in the transitive project closure,
only propext, Classical.choice and Quot.sound, no violations. Both integrations
passed; final registry closure34740 declarations and root3938 Lake jobs (cached
targets included). Seven live unittest methods passed without skips, including
three new methods with70 Lean examples (24 queue,40 metrology,6 registry).
Closure declaration counts overlap and must not be summed.

Key declarations: [continuous_phase_bound](../../Verification/PrometheusMetrologyJitter.lean#L46), [continuous_phase_variance](../../Verification/PrometheusMetrologyJitter.lean#L199),
[quadrature_covariance](../../Verification/PrometheusMetrologyJitter.lean#L185), variance_linear_functional, variance_difference,
common_mode_cancels, continuous_calibrated_error_bound, [unwrap_unique](../../Verification/PrometheusMetrologyJitter.lean#L336),
photon_average_variance, [sample_mean_with_shared_variance](../../Verification/PrometheusMetrologyJitter.lean#L265), no_photon_no_timestamp.
Registry field: QuantumPhysicsFullSuite.prometheus_metrology. Direct project import:
Verification.PrometheusChannelAndInjectorAudit. Novelty not assessed. Logs and
original failures: prometheus-pipeline-253-evidence/lean-dev. Hardware qualification,
authorization and the Third Obligation are unchanged. Final reconciled-main checks
are separate; this is not a new full beta checkpoint.

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).

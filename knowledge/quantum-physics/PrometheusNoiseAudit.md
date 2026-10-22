---
id: PrometheusNoiseAudit
language: en
section: quantum-physics
source: Verification/PrometheusNoiseAudit.lean
source_sha256: d1608470d46f047ae3550fd3d09e712b04e3a72e3a77aa2dab6ce8b8933c9b15
novelty: not-assessed
status: reviewed
---

[Lean](../../Verification/PrometheusNoiseAudit.lean)

# Conditional stopping and receiver error accounting

Epsilon245, quantum-physics/prometheus-audits. These are mathematical model
contracts; no physical device is qualified.

In a uniform medium massThickness density length=density*length, in g/cm2 for
g/cm3 and cm inputs. Geometry separates the signal chord from zenith-dependent
shield thickness; equality is not assumed. Variable-density integration is absent.
For constants a>0,b>0,E>0, stoppingRange=log(1+b/a*E)/b and
residualEnergy=max 0 ((E+a/b)*exp(-b*X)-a/b). Theorems prove the initial energy,
positivity before the threshold, zero at/after it, and the exact zero/threshold
equivalence. A detector beyond the range has a positive stopping depth strictly
before it. Range monotonicity gives E<=Ecut and X>range(Ecut) as a sufficient
condition. This constant-CSDA model excludes stochastic losses, decay and local
neutrino-induced muon production. The exponential residual is a definition of
an integrated model, not a separate differential-equation solution.

For 0<pA,pB<1 and the explicit premise joint=pA*pB, factorized_joint_bounds
proves 0<joint<min(pA,pB). Setting pC=0 does not establish independence.
The separate common-cause mixture pC+(1-pC)*pA*pB is at least pC under its sign
premises; pA,pB belong to the no-common-cause branch, not total marginals.
At pA=pB=1/100 the joint is1/10000>0. The scalar expression1-(1-p)^N is positive
for0<p<1,N>0, including p=1/10000,N=10000. Its probability interpretation needs
IID windows; no probability measure or sequential independence is derived.
Detector dead time can violate that premise.

TX contains noSignal or a bit; RX is Option Bool, with none meaning erasure.
receive forwards a candidate only with a true trigger. delivered_requires_trigger
proves necessity; a trigger may still yield erasure. Ground truth appears only in
evaluate. Every background trigger is a false alarm, even without a decoded bit;
signal outcomes distinguish correct bits, substitutions and erasures.
OutcomeMass supplies five normalized nonnegative masses. With the relevant
denominators nonzero, total_error_decomposition proves
 totalFailure = pi*(ER+(1-ER)*BER_delivered)+(1-pi)*FPR.
Here pi is signal prevalence, ER is conditioned on signal, BER on delivered bits,
and FPR on background. A zero denominator must not be treated as a defined
conditional estimate. No masses are estimated from measurements here.

Key declarations include residual_zero_iff_range_reached,
stopped_before_detector_at_energy, stopped_before_detector, factorized_joint_bounds,
explicit_many_windows, delivered_requires_trigger, background_false_alarm_iff and
verification_suite. Registry field: QuantumPhysicsFullSuite.prometheus_noise_audit.
No direct Verification imports. Original targeted verification reported168
declarations with approved axioms only;38 examples cover CSDA, paths, exact rates,
boundary cases, signal0, false triggers with erasure and distinct denominators.
The two audits and registry have3 live tests with67 examples. Historical failures
and repairs are retained; none of these counts claims a new full beta.
Zero physical background or infinite SNR is not proved. Novelty not assessed;
hardware admission, authorization and Third Obligation unchanged.

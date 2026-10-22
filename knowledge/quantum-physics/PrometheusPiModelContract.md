---
id: PrometheusPiModelContract
language: en
section: quantum-physics
source: Verification/PrometheusPiModelContract.lean
source_sha256: 105747baa66db33c1e73377858519990779c423e82832acc817295c14ee8c11d
novelty: not-assessed
status: reviewed
---

[Lean](../../Verification/PrometheusPiModelContract.lean)

# Exact scalar comparisons for Prometheus-Pi

Epsilon244, quantum-physics/prometheus-pi-model. These are conditional mathematical
comparisons. MSW focusing, sterile encoding, an OAM beam and a dual detector are
not established by this contract.

For weakCharge N Z s = N - Z(1 - 4s), the exact model input s=231/1000 gives
Q_W=13047/125 and Q_C=693/125. The tungsten square exceeds 350 carbon squares by
2137059/15625. Their ratio 18913801/53361 lies between354 and355. These are Q-squared
factors, not complete physical cross sections: kinematics, form factors, energy,
nuclei per mass and detection efficiency are unspecified. Experimental uncertainty
around the approximate input0.231 is not formalized.

In the spherical model R=6371km, minor great-circle arc D=16000km and n=73/50.
The central angle D/R is between0 and pi. Chord length is defined by the standard
formula L=2R sin(D/(2R)); a separate Euclidean sphere embedding is not constructed.
Theorems prove 0<L<=2R=12742<23360=nD. For any c>0 in consistent units,
L/c < D/(c/n), with both times positive. Generation, reception, coding, statistical
accumulation and processing latency are excluded. The proposed10800km is not this
chord's length. Numerical sine evaluation is separate; the proof uses its exact
formula and sin<=1. Likewise 1/1.46 and0.68 are different baselines.

Declarations: tungsten_charge, carbon_charge, charge_factor_margin,
charge_factor_ratio, charge_factor_advantage, central_angle_domain,
half_angle_domain, chord_distance_bounds, propagation_times_pos,
particle_time_lt_fiber_time. Proofs use exact arithmetic, Real.pi_gt_three,
positivity of sine and division by positive c. The suite exports through
QuantumPhysicsFullSuite.prometheus_pi; no direct Verification imports.

Regression examples cover independent exact values, the original c/n expression,
a positive example and necessary assumptions. At s=1/4 the350 comparison reverses;
at c=0 Lean division gives zero, so the strict inequality fails. Neither is a
physical scenario or an interpretation of division by zero as infinity.

The original targeted verification reported53 declarations with only propext,
Classical.choice and Quot.sound, and17 Lean examples in one live-test. This is
historical bounded evidence, not a new full beta. The initial numeric-bound test
normalization error and repair were retained. Conditional Python simulations are
separate evidence; binary64 and physical-device correspondence are unproved.
Novelty not assessed. Hardware admission, authorization and Third Obligation unchanged.

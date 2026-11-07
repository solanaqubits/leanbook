---
id: QuantumNoisyBBPSSWCritical
language: en
section: quantum-physics
source: Verification/QuantumNoisyBBPSSWCritical.lean
source_sha256: c3a1b888897323fb7e761bb632a885bc08ff9366f14eaebaae79f301f8c296a3
novelty: not-assessed
status: reviewed
---

# QuantumNoisyBBPSSWCritical

[Section](README.md) · [Scope](../../docs/quantum-v4.36.md) ·
[Source](../../Verification/QuantumNoisyBBPSSWCritical.lean)

This module completes the critical and subcritical orbit classification for the
constant-quality output-pair post-depolarized BBPSSW map. It reuses noisyOrbit
from v4.35 and the exact operator interpretation and fixed-point algebra of v4.34.
No new operator or placement of noise is introduced.

The critical double root is criticalFidelity=(2*criticalGamma+1)/4,
exactly (3*sqrt(5)-1)/8, strictly between 1/2 and one. At critical quality the
increment equals -2*(4F-1)*(F-criticalFidelity)^2/(9*P(F)). Fixed points on the
entire real line are exactly 1/4 and criticalFidelity.

| Critical initial fidelity | Orbit | Limit |
| --- | --- | --- |
| [0,1/4) | Strictly increasing below 1/4 | 1/4 from below |
| 1/4 | Constant | 1/4 |
| (1/4,criticalFidelity) | Strictly decreasing above 1/4 | 1/4 from above |
| criticalFidelity | Constant | criticalFidelity |
| (criticalFidelity,1] | Strictly decreasing above the double root | criticalFidelity from above |

The double root does not attract from below. The main Tendsto theorems cover
0<=F<criticalFidelity and criticalFidelity<=F<=1, including the stationary
endpoints. Interval invariants hold at every natural index. Monotone bounded
convergence, continuity and fixed-point classification identify the limits;
initial-value bounds exclude convergence to the double root from below.

For 0<=gamma<criticalGamma, every physical initial fidelity in [0,1] converges
to 1/4. When 0<gamma<criticalGamma, initial values below 1/4 strictly increase,
and those above 1/4 strictly decrease. The common low-fidelity lemmas apply
for any 0<gamma<1 and do not assume monotonicity of R on [0,1/4).
Gamma=0 is separate: noisyOrbit 0 F (n+1)=1/4 for every real F and every n.
The initial point 1/4 is already stationary at index zero.

No variable noise schedule, convergence rate, tree probability, spatial
repeater limit or resource yield is modeled. The mathematical iterations are
conditional fidelity updates of independently supplied resources.

## Theorems

- [`QuantumNoisyBBPSSWCritical.criticalFidelity_radical`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L18)
- [`QuantumNoisyBBPSSWCritical.criticalFidelity_bounds`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L22)
- [`QuantumNoisyBBPSSWCritical.critical_fixed_iff`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L27)
- [`QuantumNoisyBBPSSWCritical.critical_stationary_iff`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L31)
- [`QuantumNoisyBBPSSWCritical.critical_increment`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L40)
- [`QuantumNoisyBBPSSWCritical.critical_strict_decay`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L47)
- [`QuantumNoisyBBPSSWCritical.noisy_step_above_quarter`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L56)
- [`QuantumNoisyBBPSSWCritical.lowOrbit_invariant`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L63)
- [`QuantumNoisyBBPSSWCritical.lowOrbit_strictMono`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L73)
- [`QuantumNoisyBBPSSWCritical.critical_step_below_double`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L81)
- [`QuantumNoisyBBPSSWCritical.critical_step_above_double`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L87)
- [`QuantumNoisyBBPSSWCritical.criticalOrbit_below_double`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L101)
- [`QuantumNoisyBBPSSWCritical.criticalOrbit_above_double`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L112)
- [`QuantumNoisyBBPSSWCritical.criticalOrbit_strictAnti_below_double`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L122)
- [`QuantumNoisyBBPSSWCritical.criticalOrbit_strictAnti_above_double`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L131)
- [`QuantumNoisyBBPSSWCritical.criticalOrbit_tendsto_quarter`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L141)
- [`QuantumNoisyBBPSSWCritical.criticalOrbit_tendsto_double`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L172)
- [`QuantumNoisyBBPSSWCritical.zeroQuality_orbit_succ`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L194)
- [`QuantumNoisyBBPSSWCritical.zeroQuality_tendsto`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L197)
- [`QuantumNoisyBBPSSWCritical.subcritical_step_above_quarter`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L204)
- [`QuantumNoisyBBPSSWCritical.subcriticalOrbit_above_quarter`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L210)
- [`QuantumNoisyBBPSSWCritical.subcriticalOrbit_strictAnti`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L220)
- [`QuantumNoisyBBPSSWCritical.subcritical_stationary_iff`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L229)
- [`QuantumNoisyBBPSSWCritical.subcriticalOrbit_tendsto_quarter`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L239)
- [`QuantumNoisyBBPSSWCritical.verification_suite`](../../Verification/QuantumNoisyBBPSSWCritical.lean#L277)

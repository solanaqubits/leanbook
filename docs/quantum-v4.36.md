# Quantum v4.36: critical and subcritical noisy BBPSSW orbits

Local gamma/scoped candidate based on `10d9660aad58b61882898fcd180ad50c838d17a7`
(v4.35). Public Leanbook 1.0.0 and main remain unchanged; no push or release.

## Model and corrected critical root

The module reuses `noisyOrbit gamma F n`, iterating the v4.34 map

    R_gamma(F) = (1-gamma)/4 + gamma*R(F).

Gamma is constant. The established physical interpretation is depolarization of
the entire retained pair after ideal BBPSSW and twirling, preserving the success
probability of that step. Iteration of conditional fidelities does not compute
the probability or resource cost of a multi-round protocol.

At critical quality gamma_c=3*(sqrt(5)-1)/4, define

    F_star = criticalFidelity = (2*gamma_c+1)/4 = (3*sqrt(5)-1)/8.
    R_gamma_c(F)-F = -2*(4F-1)*(F-F_star)^2/(9*P(F)).

The exact radical formula and 1/2<F_star<1 are proved. The double root is about
0.713525, not (sqrt(5)-1)/2. Fixed points on the entire real line are exactly
1/4 and F_star. For F>1/4 other than F_star, the one-step increment is strictly
negative. In particular points between 1/4 and F_star move away from F_star.

## Critical basin classification

| Initial fidelity | Finite orbit | Limit |
| --- | --- | --- |
| [0,1/4) | Strictly increasing below 1/4 | 1/4 from below |
| 1/4 | Stationary | 1/4 |
| (1/4,F_star) | Strictly decreasing above 1/4 | 1/4 from above |
| F_star | Stationary | F_star |
| (F_star,1] | Strictly decreasing above F_star | F_star from above |

The main Filter.Tendsto theorems are:

- `criticalOrbit_tendsto_quarter`: 0<=F<F_star implies convergence to 1/4.
- `criticalOrbit_tendsto_double`: F_star<=F<=1 implies convergence to F_star.

The lower basin condition implies F<1 through F_star<1. Both stationary points
are included in the appropriate limit theorem. `critical_stationary_iff`
characterizes constant orbits with an explicit quantifier over every n.

Input monotonicity on [1/4,1] gives barriers against crossing the fixed points.
All-index invariants and strict orbit monotonicity then follow by induction.
Bounded monotone convergence gives ciSup/ciInf limits; the v4.35 continuity and
limit-is-fixed theorem reduce their identification to the two-root classification.
An initial-value bound excludes F_star as the limit when 1/4<F<F_star.
No global monotonicity in the input below 1/4 is assumed.

## Subcritical global physical basin and zero quality

For 0<=gamma<gamma_c and every F in [0,1],
`subcriticalOrbit_tendsto_quarter` proves convergence to 1/4. For strictly
positive gamma, the orbit strictly grows from below 1/4 or strictly decreases
from above 1/4. The unique stationary initial fidelity is 1/4.

Gamma=0 is separate. `zeroQuality_orbit_succ` proves

    noisyOrbit 0 F (n+1) = 1/4

for every real F and every natural n. Thus mixing is reached by the first step;
when F=1/4 the orbit is already stationary at index zero. No strict monotonicity
of the entire zero-quality orbit is asserted. Its limit theorem holds even for
nonphysical real inputs, while density-state interpretations remain physical.

## Regression coverage and validation

New kernel fixtures cover the exact critical radical formula and the rational
bounds 7/10<F_star<3/4; critical growth from F=0, decay from F=1/2 toward 1/4,
and decay from F=1 toward F_star. Both fixed endpoints and all-index barriers
are tested. At gamma=9/10 the tests cover every physical initial F through the
general limit theorem and strict monotonicity on either side of 1/4. The zero
quality fixture checks one-step absorption, Tendsto and failure of StrictMono.
The registry fixture checks `noisy_critical` and the inherited `noisy_limit`.

The module has 25 named theorems, one definition and one suite structure:
27 named exports. These are code metrics, not counts of independent scientific
results. See the [inventory](quantum-v4.36-inventory.json) and
[verification report](quantum-v4.36-verification.json).

Validation covers strict elaboration and imported axiom closure, affected
integration targets, an independent compiled-project axiom audit, targeted
container regressions, metadata and documentation. It is not a clean build,
a new full verify-all or full test discovery. The last historical full checkpoint
is v4.21 with its original qualifications; v4.25 remains a historical prototype
without a separate commit in the candidate chain. Novelty is not assessed.

No variable noise schedule, convergence rate, spatial nested-repeater limit,
multi-round success probability, resource cost or expected yield is claimed.
The spatial map H_m of v4.33 is distinct from the fidelity map iterated here.

# Quantum v4.35: noisy BBPSSW orbit basins

Local gamma/scoped candidate based on `bf09b86b62d6dbd799d76f51988f05135b7b1082`
(v4.34). Public Leanbook 1.0.0 and main remain unchanged; no push or release.

## Model and exact hypotheses

The orbit `noisyOrbit gamma F n` iterates the v4.34 map

    R_gamma(F) = (1-gamma)/4 + gamma*R(F).

Gamma is constant through the orbit. The physical basin theorems assume
`criticalGamma < gamma < 1` and `F` in `[0,1]`, with
`criticalGamma = 3*(sqrt(5)-1)/4`. The lower and upper fixed points are
`lowerWindowBound gamma` and `upperWindowCeiling gamma`, denoted F_minus and
F_plus below. The operator interpretation is the established depolarization of
the entire retained pair after ideal BBPSSW and twirling. No new operator or
noise placement is introduced. Iterating conditional fidelities does not assert
a deterministic protocol success probability or a resource yield.

## Complete seven-region classification

| Initial fidelity | Finite orbit | Limit |
| --- | --- | --- |
| [0,1/4) | Strictly increasing and below 1/4 | 1/4 from below |
| 1/4 | Stationary | 1/4 |
| (1/4,F_minus) | Strictly decreasing and above 1/4 | 1/4 from above |
| F_minus | Stationary | F_minus |
| (F_minus,F_plus) | Strictly increasing and below F_plus | F_plus from below |
| F_plus | Stationary | F_plus |
| (F_plus,1] | Strictly decreasing and above F_plus | F_plus from above |

The two main theorems are genuine `Filter.Tendsto` statements:

- `noisyOrbit_tendsto_quarter`: `0 <= F < F_minus` implies convergence to 1/4.
- `noisyOrbit_tendsto_ceiling`: `F_minus < F <= 1` implies convergence to F_plus.

The separating root itself is excluded from both basins and has a constant
orbit. The mixing and upper fixed points are included in their respective
basin statements. All interval invariants quantify over every natural index;
strict monotonicity is proved for the four nonstationary regions.

## Proof structure

Continuity holds on all real inputs, for every real gamma, by the already proved
continuity of the ideal recurrence. The low-fidelity invariant uses the ideal
barrier and the affine noise formula; it does not assume global monotonicity of
the recurrence on [0,1]. Above 1/4, strict input monotonicity and fixed points
provide barriers against crossing interval boundaries.

Bounded monotone sequences converge to their supremum or infimum. Continuity
and the shifted-orbit identity imply that any such limit is a fixed point.
Initial-value barriers exclude extraneous roots: for example an increasing
orbit in the window is at least its initial value F > F_minus, so its limit
cannot equal F_minus. The inequality is strict beyond index zero. This argument
never uses proximity to a fixed point or a numerical approximation.

## Regression coverage

At gamma=19/20, the new kernel fixtures cover growth from F=0 to 1/4,
decay from F=1/2 to 1/4, growth from F=3/4 to the exact ceiling
(29+sqrt(31))/40, and decay from F=1 to that ceiling. Symbolic fixtures cover
all-index interval barriers and all three stationary orbits. The registry
fixture checks the new `noisy_limit` field and the inherited `noisy_bbpssw` field.

## Validation scope and limitations

The module contains 23 named theorems, one definition and one suite structure:
25 named exports. These are code metrics, not counts of independent scientific
results. See the [inventory](quantum-v4.35-inventory.json) and
[verification report](quantum-v4.35-verification.json).

Validation includes strict elaboration and transitive axiom audit, the affected
integration build, independent compiled-project axiom audit, targeted container
regressions, metadata and knowledge checks. It is not a clean build, a new full
verify-all or complete test discovery. The last historical full checkpoint is
v4.21, retaining its original qualifications. The v4.25 prototype has no separate
commit in the local candidate chain. Scientific novelty is not assessed.

No orbit classification at critical or subcritical gamma, variable noise
schedule, convergence rate, spatial nested-repeater limit, resource cost or
expected yield is claimed. In particular the v4.33 spatial map is different
from the noisy BBPSSW fidelity map iterated here.

---
id: QuantumNoisyBBPSSWConvergence
language: en
section: quantum-physics
source: Verification/QuantumNoisyBBPSSWConvergence.lean
source_sha256: 12cdfce85ebf5c863e0bcc437da165cab9441d6bc4b802b68d142be3f3daac93
novelty: not-assessed
status: reviewed
---

# QuantumNoisyBBPSSWConvergence

[Section](README.md) · [Scope](../../docs/quantum-v4.35.md) ·
[Source](../../Verification/QuantumNoisyBBPSSWConvergence.lean)

The fidelity orbit iterates the existing post-depolarized BBPSSW map with a
constant real quality gamma. The two basin theorems require
criticalGamma < gamma < 1 and physical initial fidelity in [0,1].
The model and probability-preserving operator bridge come from v4.34.

Below the lower root F_minus, the orbit converges to 1/4. Above F_minus,
it converges to the upper root F_plus. The lower root itself is stationary.
These are Filter.Tendsto results, obtained by bounded monotone convergence,
continuity, fixed-point classification and initial-value barriers.
They are not based on a nearest-fixed-point rule.

| Initial fidelity | Orbit | Limit |
| --- | --- | --- |
| [0,1/4) | Strictly increasing, below 1/4 | 1/4 |
| 1/4 | Constant | 1/4 |
| (1/4,F_minus) | Strictly decreasing, above 1/4 | 1/4 |
| F_minus | Constant | F_minus |
| (F_minus,F_plus) | Strictly increasing, below F_plus | F_plus |
| F_plus | Constant | F_plus |
| (F_plus,1] | Strictly decreasing, above F_plus | F_plus |

Interval invariants hold for every natural index, including zero. The
nonstationary limit remains strictly on the indicated side at every finite
index. For an increasing orbit its initial-value lower bound is non-strict
at index zero. Input monotonicity is used only on [1/4,1]; below 1/4 the proof
uses the ideal barrier and the affine noise formula directly.

Continuity is proved on all real inputs, for every real gamma. The stationary
classification needs only gamma > criticalGamma; the physical basin statements
add gamma < 1. The module does not extend orbit classification to critical or
subcritical gamma, variable noise schedules, spatial repeater iteration,
convergence rates, or resource yield.

## Theorems

- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_zero`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L18)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_succ`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L20)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_fixed`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L24)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_stationary_iff`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L30)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_bounds`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L40)
- [`QuantumNoisyBBPSSWConvergence.continuous_noisyRecurrence`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L46)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_limit_is_fixed_point`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L49)
- [`QuantumNoisyBBPSSWConvergence.noisy_step_below_quarter`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L58)
- [`QuantumNoisyBBPSSWConvergence.noisy_step_decay_outside_window`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L70)
- [`QuantumNoisyBBPSSWConvergence.noisy_step_between_quarter_and_lower`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L88)
- [`QuantumNoisyBBPSSWConvergence.noisy_step_inside_window`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L100)
- [`QuantumNoisyBBPSSWConvergence.noisy_step_above_ceiling`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L116)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_below_quarter`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L133)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_between_quarter_and_lower`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L143)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_inside_window`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L154)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_above_ceiling`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L165)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_strictMono_below_quarter`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L176)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_strictAnti_between_quarter_and_lower`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L185)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_strictMono_inside_window`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L194)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_strictAnti_above_ceiling`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L204)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_tendsto_quarter`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L214)
- [`QuantumNoisyBBPSSWConvergence.noisyOrbit_tendsto_ceiling`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L249)
- [`QuantumNoisyBBPSSWConvergence.verification_suite`](../../Verification/QuantumNoisyBBPSSWConvergence.lean#L297)

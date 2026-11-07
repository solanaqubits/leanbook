# Quantum v4.39 — A certified noisy repeater witness

Local candidate on `2437a0830903a1ad673b4e8c330219b3d22ee4ad` (v4.38),
branch `quantum-noisy-witness-v439`. The base is local, not published main.
The separately published baseline remains `a42c09d7` (v4.21–v4.36).

[Source](../Verification/QuantumNoisyRepeaterWitness.lean) ·
[Knowledge card](../knowledge/quantum-physics/QuantumNoisyRepeaterWitness.en.md) ·
[Inventory](quantum-v4.39-inventory.json)

## Fixed model and statement

The witness uses constant output-pair post-depolarization quality gamma=19/20,
initial Visibility 4/5 and chronological schedule 16 then 16. The spatial step
is the existing ideal pairSwap followed by the noisy binary BBPSSW tree. This
module changes neither the channel nor the v4.38 operator and accumulator.

The first level's depth 16 strictly exceeds 4/5; every smaller depth stays below
4/5. Starting from that particular first output, the second level's depth 16
strictly exceeds the first output; every smaller second depth stays below it.
The depth-15 second output even stays below the original 4/5. The targets are
therefore explicitly different at the two levels.

These are input-specific minimum depths. They do not prove global optimality
among all schedules, a discontinuous depth law as a function of noise, or a
minimum expected resource cost. The ideal schedule 4 then 2 is a separate
previously checked witness, not a noisy alternative with the same guarantee.

## Interval proof rather than a floating-point assumption

The source proves monotonicity of noisyRecurrence gamma on [1/4,1] whenever
gamma>=0. A general interval-step lemma combines that monotonicity with proved
lower and upper endpoint inequalities and preservation of the physical domain.

Two chains of 16 steps use outward-rounded rational endpoints on a 10^-8 grid.
Every endpoint transition is discharged by norm_num inside Lean. No external
numeric result is trusted, no native_decide is used, and no proof limit is raised.
The first initial fidelity is exactly 73/100. The second initial fidelity is
bounded from the proved first visibility enclosure, not a decimal approximation
substituted for the actual first state.

| Quantity | Certified lower bound | Certified upper bound |
| --- | --- | --- |
| First-level F at depth 15 | 0.84911037 | 0.84911044 |
| First-level F at depth 16 | 0.85169269 | 0.85169275 |
| Second-level F at depth 15 | 0.84975023 | 0.84975040 |
| Second-level F at depth 16 | 0.85222959 | 0.85222975 |
| First output visibility | 0.8022568 | 0.8022572 |
| Second output visibility | 0.8029727 | 0.8029731 |

The decimals in this table denote exact terminating rationals. Both actual
swapped inputs lie inside the supercritical working window. Strict monotonicity
of each fidelity orbit bounds every depth below 16 by its depth-15 value. This
turns the certified endpoint bounds into quantified minimum-depth statements.

## Operator and resource consequences

The witness proves LocalQualityGain from the two strict gains, and both nonempty
prefixes strictly exceed initial quality. The v4.38 refinement identifies the
actual unnormalized matrix with p*isotropic(secondLevelVisibility), proves PSD,
0<p<=1 and trace p, and normalizes it to a PSD matrix of trace one.

There are exactly four spatial segments and

    2^17 * 2^17 = 2^34 = 17179869184

independently prepared raw pairs. This is the leaf count of the fixed all-success
tree. It is not a retry model, expected pair count, probability of success or a
positive asymptotic generation rate. Output normalization does not assert purity.

## Verification scope

The gamma/scoped plan covers the complete quantum direction, affected external
consumers, registry integration and explicit live regressions. The new module
receives strict CLI checking and an imported-closure axiom audit; a pinned separate
auditor checks compiled project declarations. The final container uses 12 GiB,
four CPUs and zero swap. Exact commands, interval data and all logs are in the
external synchronization package. The incremental cache is retained.

Allowed axioms remain propext, Classical.choice and Quot.sound. No new full
verify-all, beta checkpoint, publication or release tag is claimed. Variable
noise, asymmetric input buffering, noisy swapping, arbitrary gate errors,
adaptive depth selection and global schedule optimization remain outside scope.

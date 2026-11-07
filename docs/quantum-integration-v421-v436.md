# Quantum v4.21–v4.36 integration

This integration brings the verified local quantum chain into the Leanbook main
line based on public commit `5276529c6c1010722cc96c39217892b9e874f6a8`.
The candidate chain ends at `7981d0f6e1ec9dfda342eb32a8ad312a53b6ef30`.
It contains fifteen commits adding twenty formal modules. v4.25 is a historical
prototype, not a separate commit. Existing theorem statements and proofs, toolchain, dependency manifest and
verification mechanisms are unchanged. Integration adds documentation and restores
the missing license header of QuantumAdaptiveWernerCascade, as required by the
hosted style linter; its mathematical body is byte-for-byte unchanged.

## Formal coverage

- v4.21–v4.24: correlated system/environment inputs, decoupled reduction,
  independent stages, post-analyzer coupling and CPTP post-processing.
- v4.26–v4.28: two-round instruments, Werner reduction, adaptive delivered-message
  feedback, faithful detector loss, weighted conditional states and trace balance.
- v4.29–v4.31: constructive twelve-operation Clifford twirling, operator BBPSSW,
  ideal orbit limits, binary resource-tree probabilities, heterogeneous inputs
  and the operator bridge between swapping and distillation.
- v4.32–v4.33: finite repeater trees, nested purification depth, resource counts,
  one-round visibility decay and finite-scale quality preservation after a gain.
- v4.34–v4.36: post-depolarized BBPSSW, fixed points and complete physical orbit
  classification for constant quality 0<=gamma<1. Ideal gamma=1 is covered by
  v4.30. These temporal fidelity iterates are not spatial repeater-map iterates.

The last three modules have 90 named theorems and 102 named exports. Counts are
code metrics, not independent scientific results. Each stage retains its source
inventory, precise assumptions, regression tests and original scoped report.

## Noisy orbit classification

The model applies a depolarizing channel to the entire retained pair after ideal
BBPSSW and twirling. The success probability remains P(F), and
R_gamma(F)=(1-gamma)/4+gamma*R(F). It does not model arbitrary errors inside CNOT.
Let gamma_c=3*(sqrt(5)-1)/4 and F_star=(3*sqrt(5)-1)/8. For 0<=F0<=1:

- 0<=gamma<gamma_c: all orbits converge to 1/4. At gamma=0, every index n>=1
  equals 1/4; F0=1/4 is already stationary at index zero.
- gamma=gamma_c: starts below F_star converge to 1/4; starts at or above F_star
  converge to F_star. The double root attracts from above, not from below.
- gamma_c<gamma<1: starts below F_minus converge to 1/4; starts above F_minus
  converge to F_plus. The separating F_minus is stationary, as are 1/4 and F_plus.

The critical and supercritical limits are Filter.Tendsto theorems, not numerical
fits. Invariance and strict orbit monotonicity apply to their stated nonstationary
regions. No variable quality schedule, convergence rate or expected yield is claimed.

## Integration verification

The reviewed planner uses gamma scope for quantum-physics against the actual
public parent. Reverse dependencies expand the checked directions to
numeric-certificates. It selects all members of those affected directions,
builds registry consumers, and audits maximal importing roots. An independently
implemented, pinned auditor checks the compiled project axioms. Every proof
source is compared with the previously checked candidate; no proof is weakened
or replaced to enable integration.

The integration test selection includes every unittest module with live Lean
checks enabled, in the qualified 12 GiB / 4 CPU / swap=0 container, including the
pinned SQLite and native cryptographic profiles. This broader test coverage does
not turn the proof scope into a new beta checkpoint. Command logs, environment
fingerprints, the source identity manifest and final outcomes accompany the
integration handoff. Hosted CI runs its own configured checks on the pushed head.

Allowed axioms remain propext, Classical.choice and Quot.sound; no sorryAx or
native-decide bypass is permitted. Metadata, knowledge links and whitespace are
checked. Historical per-stage counts are not summed as independent audit coverage.

No release tag is created or moved. Leanbook v1.0.0 and its published artifacts
remain unchanged; main gains the integrated source development. This work does
not claim a new clean full-library beta checkpoint or universal correspondence
between formal statements and every physical implementation.

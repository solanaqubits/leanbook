# Quantum v4.20: mixed environments and Bell instruments

This component publication adds 31 quantum modules developed since the preceding
public snapshot. It is a scoped quantum update, not a new whole-library beta checkpoint.
Existing public leaf proof sources and the pinned toolchain/dependencies are preserved;
the registry is extended additively.

The series covers four-phase Pauli matrix semantics, density operators, Born-derived
Bell measurement, noisy classical readout, rectangular Kraus instruments, null branches,
noise transport through gate sequences, retained environments and explicit memory/reset
counterexamples. The final two modules add arbitrary fixed mixed independent environments,
CPTP reduction, ensemble-independent semantics and branchwise BSM refinement.

## Final v4.20 obligation

`QuantumMixedEnvironment` has 12 named theorems. A PSD trace-one environment matrix σ
is factored using its positive square root. Preparation operators Jₜ satisfy
∑Jₜ ρ Jₜ† = ρ⊗σ and ∑Jₜ†Jₜ = I. For any joint CPTP channel E, operators
select(r) Eₖ Jₜ define a reduced CPTP channel whose action is Tr_env E(ρ⊗σ).
The result is independent of an ensemble representation of σ. A regression compares
the Z- and X-basis decompositions of I₂/2 for an arbitrary joint E.

`QuantumMixedMemoryBSM` has 20 named theorems. Direct microscopic, rejection and
reported branches agree with final partial traces of joint operators on ρ⊗σ.
Under the stated ideal-circuit-factorization hypothesis they refine the five-outcome
instrument after the effective input channel. CP, total trace and zero-branch behavior
are preserved. Pure-basis preparation and an unused mixed environment recover the
previous contracts, including the impossible GHZ Ψ⁺ branch.

## Verification

Public-tree evidence is recorded in `quantum-v4.20-verification.json`.
Strict module and registry builds, a transitive axiom audit, the dependent root build,
quantum regressions, metadata and knowledge checks are run on this public candidate.
An initial cold build reached its 600-second timeout on an unchanged photonic dependency.
Its prior public artifact was reused after matching its six-source closure, toolchain
and dependency lock; Lake freshness checks and the new public axiom audit remained enabled.
The allowed standard axioms are propext, Classical.choice and Quot.sound.
No sorryAx, additional axioms or native-decide shortcuts are permitted.
The public registration linter required standard Apache-2.0 headers on the newly
published sources. These comment-only fixes were synchronized with the private source;
no definitions or proof terms were changed. Private development logs, Russian working
notes and private Git history are not exported.

## Limits

The initial state is a product ρ⊗σ. Arbitrary initial system-environment correlations,
adaptive interventions and process tensors are separate open obligations. The ideal
instrument hypothesis and each specified noise location remain explicit. No universal
fidelity degradation, physical parameter calibration or experimental breakthrough is
claimed. The noncomputable square-root construction is not a numerical simulator.
Novelty: not assessed.

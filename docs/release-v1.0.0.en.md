# Leanbook 1.0.0

This global release consolidates the public mathematical library, its verifier,
knowledge cards, registered contracts and the Quantum v4.5–v4.20 development.
It advances the global alpha counter under VERSIONING.md. It is distinct from
Geek Work / SimLab 1.0.0 and from the scoped quantum-v4.20 component tag.

## Included work

The public catalog contains 377 modules in 12 sections plus 3 support modules.
There are 381 library Lean source files including Verification.lean and nested
specifications, two executable roots, and 331 direct MasterSuite imports.
These different metrics must not be added together.

All 31 modules and 619 named theorem declarations from the quantum development
are included, with source hashes and declaration locations in
[the inventory](quantum-v1.0.0-inventory.json). Highlights:

- Four-phase Pauli operators and matrix soundness, density operators and CPTP maps.
- Born-derived Bell branches, readout confusion, Bell-diagonal convolution and
  Werner visibility; coherent GHZ counterexamples to universal uniform outcomes.
- Rectangular Kraus maps on arbitrary four-qubit inputs, five-outcome instruments,
  zero-probability branches and safe conditional normalization.
- Pre/post gate noise, ordered and multistage composition, noise transport and
  explicit witnesses distinguishing physical outcomes from classical messages.
- Retained environments, memory/reset counterexamples, arbitrary fixed mixed
  independent environments and branchwise BSM refinement. The final pair,
  QuantumMixedEnvironment and QuantumMixedMemoryBSM, contributes 32 theorems.

The existing cryptography, distributed systems, photonics, finance and other
public components remain included. See the catalog for assumptions and scope;
this release does not export unrelated private work or private Git history.

## Compatibility and migration

The Lake package identifier remains `lean-verification-components`; its version
is now 1.0.0. Existing imports, definitions and theorem statements are preserved.
Lean 4.33.1, Mathlib and lake-manifest.json remain pinned.
The 15 new quantum test launchers now use the shared configured Lake invocation,
so project compiler options are inherited. Seven long fixture lines are wrapped
to satisfy the enabled style linter; assertions and proof expressions are unchanged.
The initial full test pass detected the older unconfigured invocation; that
attempt is not treated as release qualification. Consumers may pin
`v1.0.0` instead of their earlier public revision without an import rename.
Consumers of the new quantum modules must still supply each theorem's premises.
A major publication is not a promise to preserve every implementation detail in
future major versions. Historical tags and their verification records are retained.

## Release gate and evidence

Publication requires a schema-3 full release report: a fresh project-only strict
build of every library module and both executables, verify-all, registry and
pinned independent axiom audits, all live tests including the pinned native store
profile, knowledge checks, scope checks and whitespace checks. Shared dependency
artifacts are mounted read-only and are not rebuilt. The report binds exact
source/configuration/test bytes, toolchain and dependencies. Source inventories,
fresh compilation counts, audit declarations and test counts are separate metrics.

The release assets provide the actual results, logs and SHA-256 manifest. Until
that gate passes, this source tree is a release candidate, not a qualified release.
Only propext, Classical.choice and Quot.sound are allowed; sorryAx and additional
axioms are forbidden. The independent auditor is a distinct audit implementation,
not a second independent proof kernel. Registered Simon and qutrit specification
checks do not establish universal semantic conformance of every module.

## Scientific and operational limits

Claims apply to the precise definitions and hypotheses in Lean. They do not
certify fabricated news, physical devices, measured constants or hardware safety.
For the latest mixed-environment construction, the initial state is a product
rho tensor sigma; arbitrary initial correlations, adaptive interventions and
process tensors remain separate obligations. Noise locations and ideal-circuit
factorization hypotheses remain explicit. No universal fidelity decrease or
experimental realization is claimed. Novelty is not assessed.

Native tests cover the pinned local profile; they do not establish cryptographic
security, hardware authorization or production readiness. Reservoir indexing is
not established by this release.

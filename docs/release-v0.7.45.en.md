# v0.7.45 — profile bytes, manifests and conditional models

This cumulative release extends v0.7.44 with epsilon243–248: QCP/01 canonical
finite-profile bytes and a bounded reader/CLI; the QPM/01 canonical provenance
manifest; and Prometheus-Pi, noise, UCN and p-B11 conditional scalar contracts.
There are 250 direct MasterSuite imports and 294 Lean source files including
Verification.lean. Previously published tags remain unchanged.

QCP/01 has strict decoding, size/count limits, round-trip and canonicality proofs,
and a restoration equivalence under an independent expected context. Its
[reader](quota-profile-reader.en.md) decodes accumulated bytes only after EOF.
QPM/01 proves round-trip, canonicality and injectivity of encoding and the fixed
prefix signing message. It implements neither hashing nor Ed25519 verification,
key authorization, revocation, trusted time or atomic replay consumption.

The physics modules prove conditional scalar identities and inequalities:
weak-charge-square comparisons and spherical-route propagation; constant-medium
stopping and receiver error accounting; conditional UCN kinetics and mass/energy
bookkeeping; and p-B11 shot energy conservation and extraction bounds. Model inputs
and their physical interpretations remain explicit premises. These proofs do not
qualify a detector, communication system, reactor or energy-producing device.

Public acceptance checks include strict Lake builds with an explicit qutrit Spec,
all live-enabled public unittest, catalog validation, the transitive union axiom
audit and a pinned independent axiom-dependency audit. Only propext,
Classical.choice and Quot.sound are allowed; native_decide is not admitted.
Exact executed results and main/tag CI outcomes are attached to the GitHub release.
Local checks use a memory ceiling of 8 GiB and shared Mathlib artifacts.

The full public beta baseline remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); Lake remains 0.7.1.
No new beta baseline/tag is allocated. Test/audit counts are evidence for the
specified checks, not exhaustive semantic correctness or physical provenance.
Authorization remains blocked. Hardware qualification is outside this release.

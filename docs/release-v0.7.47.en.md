# v0.7.47: provenance reports, explicit native IO and replay recovery

This release exports the integrated development snapshot for epsilon258–259
and the native provenance IO layer; reserved or unintegrated modules are excluded.

- Granular reports separate limits, key/role/revocation checks, signatures,
  artifact hashes, context, challenge and time-policy results. Data-only preflight
  suppresses backend calls on limit refusal. Report production is not acceptance.
- The explicit IO/FFI adapter qualifies an exact libsodium binary and executes
  detached PureEd25519/SHA-256 requests. Fixed known-answer, malformed-input,
  failure-injection and observed-request tests accompany the native code.
  It is excluded from the pure Verification import graph.
- Replay recovery uses prepare, completed persist, trusted-prefix commit,
  acknowledgement, crash and recovery events. Reachability proves retention of
  acknowledged challenges, including the protected base, and refusal of replay
  after accepted restoration. Exact completed-image recovery is separate from
  prefix-only validation, which can accept unauthenticated suffixes.

261 direct MasterSuite imports and 305 Lean sources including Verification.lean
are byte-identical to the pinned development snapshot. The new native toolchain
and CI configuration require full beta-level public validation: strict Lake,
explicit qutrit Spec, verify-all, registry and independent audits, all live tests
and catalog checks. Local checks run under an 8 GiB cgroup. Resource-only Lean
single-thread elaboration preserves kernel checks. Actual check results are recorded
in the release receipt; this document does not substitute for those results.

CI uses Ubuntu24.04 and installs the exact qualified libsodium23 package, then
checks the committed binary SHA-256 before running native tests. A changed binary
fails closed and requires explicit requalification. No automatic profile updates
or skipped native tests are permitted. The adapter itself does not install packages.

No physical durability, trusted-anchor implementation, concurrency, exactly-once
network delivery, universal malformed-input coverage, cryptographic strength,
side-channel safety, FFI refinement or hardware authorization is proved.
Authorization stays blocked. The pure recovery result depends on retained completed
data and the independently protected prefix; serialization alone cannot prevent rollback.

The designated full public beta baseline remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); Lake remains0.7.1.
A new beta tag/baseline is not allocated. Private logs, archives and organizational
materials are excluded from this public export.

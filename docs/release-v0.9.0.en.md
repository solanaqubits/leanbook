# v0.9.0 — 300 direct MasterSuite imports

This beta checkpoint extends the public v0.8.0 base
`7f68d8e577136ba3729643e4a57ad740a668670d` with thirteen mathematical modules:
eight in cryptographic algebra and five in finance. The
[extension record](toward-300.en.md) lists their contracts and limitations.
The existing ALCC stack and toolchain are unchanged.

## Counting and scope

There are 300 direct imports in `Verification/MasterSuite.lean`, up from 287.
This is not an allocation of global epsilon identifiers or a count of independent
security theorems. The library has 349 Lean sources including `Verification.lean`;
the CLI, auxiliary Lean tools and test fixtures are outside that metric.

The additions contain 106 theorem declarations, including suite constructors,
and 106 Lean regression examples. Each module has an English scope card and an
integration recipe. The new contracts cover polynomial sharing and refresh,
typed pairing equations, stateful AMM routes, integer rounding and lending
utilization transitions. They do not claim complete deployed protocol security,
SNARK knowledge soundness, compatible token units or machine-overflow refinement.

## Accepted validation

The full local beta gate is bound to source commit
`ec290046edcd9a345bdf4dbab1456e892c47f0ea`:

- Strict incremental `lake build --wfail`: 4,089 Lake jobs, with cached targets
  retained; this is not a clean rebuild of every dependency.
- Whole-library source verification: all 348 modules under `Verification/`.
- Project and pinned independent axiom auditors: 40,333 declarations each;
  only `propext`, `Classical.choice` and `Quot.sound`, without violations.
- All 606 tests passed, with no skips, including target-qualified SQLite tests.
- Catalog, local links, dependency scope and source consistency checks passed.

The accepted beta evidence digest is
`74494ed28ad663036654e8653ece0a3a6daaa2f1c56bd6408bcc2c22d433f7ee`.
Subsequent changes are documentation only, checked separately against the bound
source/test/configuration hashes. The release asset `validation-public.json`
records the final publication commit and the scope of evidence reuse.

Two setup attempts were interrupted before the accepted test run: first to
qualify the runtime environment, then to build the missing native transport.
Completed formal checks were reused only after source and runtime fingerprint
comparison. The entire test suite was rerun after the native setup correction.

Hosted CI runs separately and retains its documented exclusion of target-specific
SQLite tests. Its status does not replace the full local gate. Neither the two
auditors nor the tests establish independent semantic conformance of every
module: the registered Simon and qutrit contracts have that narrower coverage.

## Publication boundary

This release publishes Leanbook source additions and documentation. SimLab's
existing public ALCC integration is unchanged; no new SimLab release is required.
Historical tags, private proof-mode branches and operational authorization
settings are preserved. Hashes establish consistency and traceability, not
publisher authenticity or bit-for-bit build reproducibility.

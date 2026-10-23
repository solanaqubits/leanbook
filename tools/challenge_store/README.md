# Local SQLite challenge registry (runtime adapter)

This is an explicit IO adapter for the existing pure ε262 model, not a new Lean
proof of SQLite. It uses Python's native `sqlite3` extension (SQLite C library)
and a bounded private pipe to Lean. No new C wrapper is needed. The Lean worker
obtains native PureEd25519/SHA-256 answers through the existing explicit IO/FFI
adapter, constructs a finite pure response model, and evaluates ε262 `step`.
Neither the worker nor the store accepts client-supplied positive reports.

## Build and use

The current application profile requires the isolated corrected SQLite runtime.
See [RUNTIME.en.md](RUNTIME.en.md) for install/check and the anchored CLI launcher.
Direct Python/API/test invocations require the qualified library in the loader
environment **before** interpreter startup. Existing system SQLite is refused.
`checkpoint_profile_v1.json` preserves the previous checkpoint identity separately
from `profile.json`, which qualifies the actually executed library.

From the Leanbook root, with the shared Mathlib packages already linked:

```sh
python3 -m tools.challenge_store.build
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest tests.test_challenge_store -v
python3 -m tools.challenge_store.cli --db /absolute/path/registry.db inspect
```

Trusted application code initializes the database and retains the controller
capability. Workers get ordinary Store instances without that capability:

```python
from tools.challenge_store.store import Store, Controller
controller = Controller()
Store.initialize('/private/local/registry.db', controller)
with Store('/private/local/registry.db', controller=controller) as registry:
    registry.install_context('immutable-version-1', trusted_config, controller)
    registry.issue(request['key'], controller)
    registry.register('preselected-transaction-id', request)
    result = registry.commit_checked('preselected-transaction-id', request)
    resolution = registry.resolve(request['key'], 'preselected-transaction-id')
```

`trusted_config` and `request` use the JSON fields of `ContextConfig` and `Request`
in `Wire.lean`: byte arrays are lists of integers 0..255; rationals are canonical
`[numerator, positive_denominator]`; enum/structure encodings follow Lean's derived
JSON instances. `fixtures.py` gives a complete synthetic example using an explicitly
public test seed. Never use this seed as a real signing identity. There is no signing
service in the production store.

The CLI offers register/commit/resolve/lookup with `--input FILE` and inspect.
Input is `{ "txId": "...", "request": ... }` for register/commit,
`{ "txId": "...", "key": ... }` for resolve, and `{ "key": ... }` for lookup.
CLI success means an operation returned a result, not that evidence was accepted.
Administrative installation, issuance and cancellation remain the trusted Python API.
The capability separates trusted application paths, not mutually hostile Python code.
The database directory, process, loader, modules and profiles must be trusted; a
process with direct write access to the database can bypass this application boundary.

## Transactions and mapping

`BEGIN IMMEDIATE` serializes installation, issuance, registration, commit and abort.
The model result, consumed entry and terminal outcome are written in one SQL commit.
SQLite manages its own locks; the adapter never manually locks WAL. Immutable versions
include the complete ExpectedContext, VerificationLimits and missing-time policy.
Active pointers are per context/session/policy; installed versions cannot be reactivated.
Pending transactions bind the exact message bytes and full challenge key. They may
reference unissued challenges. COMMITTED transactions must reference a consumed entry.

The adapter reconstructs finite maps from four relational tables, validates their
shape, compares the stored post-state to the Lean result before COMMIT, and preserves
an acceptance sequence number for the model's ghost acceptance list. Its local adapter
limits are 2048 rows per table, 8 MiB wire frames and a bounded materialized input;
these are operational refusal limits, not formal time/memory proofs. Existing state
is never pruned to free capacity. Larger deployments require a separately reviewed
profile/migration; this v1 intentionally favors inspectability over throughput.

`register` on an existing identical binding returns administrative false, matching
ε262; conflicting bindings raise `transaction_binding_mismatch`. Model-level commit
conflicts remain `rejected transaction_conflict`. `resolve` checks the supplied key;
it cannot check message bytes absent from its arguments. A wrong key is an adapter
error rather than ε262's uninformative `still_indeterminate`.

Historical returns rebind the presented artifacts to the signed manifest using the
pinned original context and limits. They preserve the original report and do not
revalidate the new signature, current revocation list or current time policy.
A retry failure never changes a prior terminal transaction. A new transaction may
record a historical return; it does not add a new acceptance event.

`abort_pending(key, tx, controller)` returns aborted/already_aborted/already_committed/
transaction_not_found. It never invents a tombstone for an unknown ID. A late executor
reads ABORTED inside its write transaction and cannot commit. `resolve` only reads:
absent/pending means still_indeterminate; only recorded ABORTED confirms not committed.
A SQL rollback is not an application ABORTED outcome. Commit acknowledgement failure
raises `StoreError('indeterminate_transaction_state')`; callers resolve the existing ID.
No automatic retry assigns a new ID or silently repeats an acceptance.

## Qualification and conformance

`profile.json` pins SQLite version/source ID, actual mapped library path and SHA-256,
and the CPython native extension hash. Connections require WAL, synchronous FULL,
foreign keys and recursive triggers. The schema, triggers, quick_check and foreign
keys are checked. Failures do not silently create or migrate an existing database.
Binary qualification assumes trusted local files; it is not filesystem race protection.

Tests cover the eleven approved groups: registration; issuance; admission; contexts;
historical retry; multiple processes; abort; crash recovery; resolve; structural
constraints; administrative access/blocked authorization. Native library failures
and independent RFC/NIST vectors remain covered by `tests.test_provenance_native`.
The new store suite uses real signatures over synthetic manifests and fixed native
answers, not physical measurements. Fault injection is explicitly labeled.

`conformance.check_history` searches for a model ordering of each captured completed
history that respects nonoverlapping calls. Budget exhaustion/incomplete histories
produce inconclusive. This is finite conformance testing, not a general linearizability
proof. Sequential replay checks SQLite projection against ε262; both use the same
Lean semantics, so it is not independent semantic verification of that model.

SIGKILL tests exercise process failure before commit and after commit before response.
They are not power-loss tests. No formal proof of C/Python/compiler/VFS correctness,
crypto security, physical provenance, database anti-rollback or hard resource bound
is supplied. External independent anchors remain necessary for anti-rollback.
`authorization = blocked`, hardware PAUSED and Third Obligation OPEN remain unchanged.
No public export/release is performed by this adapter.

Primary implementation references (consulted during development):
- https://www.sqlite.org/lang_transaction.html
- https://www.sqlite.org/pragma.html#pragma_synchronous
- https://www.sqlite.org/foreignkeys.html

## Four-file QPM/01 submission

The file path adapter accepts a manifest file, a detached signature, and two raw
artifact files. It obtains the complete trusted configuration from an independently
installed immutable database version. It does not derive expected roles, session,
policy or challenge from the package.

```python
from pathlib import Path
from tools.challenge_store.files import FilePackage, submit_files
with Store('/private/local/registry.db') as registry:
    result = submit_files(registry, 'client-selected-id', 'immutable-version-1',
        FilePackage(Path('manifest.bytes'), Path('signature.bytes'),
                    Path('snapshot.bytes'), Path('profile.bytes')))
```

Equivalent trusted-host CLI (the JSON file contains only `{"txId":"client-selected-id"}`):

```sh
python3 -m tools.challenge_store.cli --db /private/local/registry.db submit-files \
  --context-version immutable-version-1 --input transaction.json \
  --manifest manifest.bytes --signature signature.bytes \
  --snapshot snapshot.bytes --profile profile.bytes
```

All four regular files are read from an open descriptor in bounded chunks until
EOF; at most limit+1 bytes are read to detect an over-limit input. The signature
must have exactly 64 bytes. Manifest/artifact caps come from VerificationLimits,
with an additional local operational cap of 128 KiB per file for the bounded JSON
transport. Input above this adapter cap is refused even if policy permits more.
Directories, devices and FIFOs are rejected. O_NONBLOCK is used while opening so
a FIFO does not hang before type checking. This does not establish a hard time bound
for filesystem operations, nor protection against a hostile filesystem or memory OOM.

`strictDecodeManifest` runs on the original QPM/01 bytes. The resulting manifest
crosses the actual Lean→Python→Lean JSON bridge; a second strict decode compares
all fields, then signingMessageV1 bytes. Runtime comparisons are not new universal
JSON round-trip proofs. The typed request uses the external expected key and is
checked against input limits before registration. Files are never reopened after
registration: crypto verification and storage operate on those exact loaded bytes.

Reading, decoding, bridge or preflight-limit errors raise FileInputError and never
register a transaction. In isolation, all four logical tables remain equal; another
worker may legitimately change them concurrently. Crypto/content refusals after
registration may record ABORTED while leaving the challenge unconsumed. register
and commit are separate transactions: a crash between them leaves recoverable PENDING.
Old-ID retries retain NEW_ACCEPTANCE; successful new-ID retries record HISTORICAL_RETURN.

`tests/data/provenance_files/vectors` contains fixed binary input, independently
encoded/signed fixtures, expected decoded fields, complete reports and exact SQL row
snapshots. cryptography/OpenSSL generated the public RFC8032 test-key signatures;
replay uses libsodium and never regenerates or signs fixtures. Unicode, large integer
and negative rational/time fields exercise the structural bridge. The JSON fixture
context is installed separately by the test controller, never read from the package
by the production adapter. Artifact bytes are synthetic: this path checks their
signed hashes/sizes, not QCS/QCP decoding or cursor mathematical validity.

## Optional external witness boundary

`AnchoredStore` adds a fail-closed external checkpoint protocol to the same API,
including `submit_files`. It requires a separately supplied trusted `Witness` and
independently pinned identity. No production external service is configured by
this repository; the original Store/CLI does not silently change behavior.
See [ANCHOR.md](ANCHOR.md) for provisioning, Ready/Prepared transitions, recovery,
blocking crash windows and deployment assumptions. Tests use an unqualified
reference service and do not close the external Anti-Rollback trust obligation.

`HTTPSWitness` now supplies an explicit TLS 1.3/mTLS client for a separately provided
service. See [WITNESS_HTTPS.md](WITNESS_HTTPS.md) for exact wire fields, certificate
pinning, failure semantics and remaining external durability/freshness obligations.
The loopback conformance fixture is not a production anti-rollback trust anchor.

## Trusted Witness deployment configuration

Use `python3 -m tools.challenge_store.witness_config check-config` for explicit pinned
local configuration validation, or `probe` for one read-only TLS observation. Both
require `--config` and an independently trusted `--config-sha256`. Neither enrolls a
store or authorizes writes. See [WITNESS_OPERATIONS.md](WITNESS_OPERATIONS.md) for the
schema, file policy, report meanings, rotation and external qualification obligations.

For operational commands explicitly guarded by that Witness, use the separate
`python3 -m tools.challenge_store.anchored_cli` entry point. It supports `inspect`,
`lookup`, `resolve` and `submit-files` with mandatory pinned configuration and no
plain fallback. See [ANCHORED_CLI.md](ANCHORED_CLI.md). The original CLI remains plain.

The consolidated [deployment procedure](DEPLOYMENT.en.md) separates runtime/provider
qualification, operator responsibilities, acceptance evidence and recovery. Its
[acceptance worksheet](DEPLOYMENT_ACCEPTANCE.json) is unfilled documentation, not
an executable permission mechanism or production connection.

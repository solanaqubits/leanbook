# Clean project graph before beta qualification

The clean build replaces the initial incremental root build in beta evidence
schema **2**. Historical schema 1 evidence is retained, but cannot qualify a new
beta. Ordinary development remains incremental.

## Scope and freshness

`tools/clean_project_build.py` derives a plan from the checked `lakefile.toml`:
all sources in each declared library, each library root, every executable root
and every executable target. On this candidate that is **352 modules**:
349 under `Verification/`, root `Verification`, `AlccVerifyMain` and
`AlccNormalizeBench`; there are two executable targets. Arbitrary custom Lake
layouts/configurations are rejected rather than guessed. Unregistered test and
tool scripts are still handled by their separate test/build gates.

The script removes the entire checkout-local `.lake/build`, including metadata,
intermediate code, native objects and executables, and records an empty start.
It rejects symlinked project build directories. It never cleans `.lake/packages`.
Dependency directories must already exist and be mounted read-only. Their build
files are hashed before and after the run. No dependency download or rebuild is
authorized; a missing dependency artifact must cause failure.

Lake receives `--no-cache` and environment settings `LAKE_ARTIFACT_CACHE=false`,
`LAKE_CACHE_DIR=` and `LAKE_NO_CACHE=true` to prevent project artifact restoration.
All module/executable targets are explicit; `--verbose --no-ansi` retains per-job
Built/Replayed evidence. Strict warnings remain failures.

Success requires every planned module to appear as freshly Built, none as
Replayed, an exact `.olean` module set, fresh `.olean`, `.ilean`, module `.trace`
and generated `.c` for every module, and each executable. Timestamps are checked
against the empty-start boundary; hashes of *all* project build files (including
objects and metadata) and each module's trace depHash are recorded. Identical
hashes to a previous build are allowed: deterministic output is not stale output.

The reused dependency count is the number of distinct manifest packages with
module Replayed entries in this run and matching preserved artifacts. It is not
the number of dependency jobs, nor proof that every module in a package was used.
The full pre/post dependency artifact maps are retained alongside this count.

## Local pinned container

```sh
python3 tools/clean_build_container.py \
  --image sha256:LOCAL_INSTALLED_IMAGE_ID \
  --output /absolute/new/build-evidence
```

Use the full ID of an already installed, compatible Linux image. The launcher
never pulls an image. It binds host system libraries and the selected Lean
toolchain read-only, so the image ID alone does not identify the complete runtime.
Package paths and their resolved targets are mounted read-only; the isolated
project and evidence directory are writable. Source hashes must remain unchanged.

Limits: network none, 12 GiB container memory with no swap, 4 CPUs, 512 PIDs,
512 MiB tmpfs; Lake child timeout 3600 seconds, outer container wait 3700 seconds.
The launcher records its exact command, inspect output, logs and exit status,
and removes only its own uniquely named container after completion. This is a
Lean build launcher, not the separately planned SimLab benchmark watchdog.

The receipt can be rechecked on the host:

```sh
PYTHONPATH=tools python3 -c 'from clean_project_build import validate_receipt; \
from pathlib import Path; print(validate_receipt(Path.cwd(), \
Path("/absolute/build-evidence/clean-project"))["status"])'
```

`release_evidence.py run-beta` invokes the clean-project builder first and binds
its receipt hash. Run that full gate in a suitably mounted environment too.
The independent auditor, all live tests, registered conformance checks and catalog
checks remain required; a successful clean build alone is **not** a new beta.

Receipts are unsigned execution records. Hash checks do not authenticate the
operator, prove source/compiler correspondence, or eliminate concurrent hostile
writers. Use an isolated worktree, preserve failure receipts, and independently
review the source, logs and final evidence before publication.

### Full beta runtime preparation

Beta evidence schema 3 includes a mandatory `native-build` step after the axiom
checks and before the full tests. It builds the SQLite/native challenge-store
transport from the checked sources; both Lean and provenance-store live-test
flags are enabled by the gate. A fresh checkout must not rely on a transport
left over from an earlier test run.

The initial clean build still requires exact equality of planned and emitted
project modules. Final receipt validation permits only five explicitly
named runtime helper modules: challenge-store `Wire`, `FileManifest`, `Worker`,
and provenance-native `Raw`, `Adapter`, added by native preparation and tests. It still rejects missing planned modules, unexpected
modules, and any change to a frozen clean-build artifact. These helper modules
are runtime infrastructure, not additions to the audited formal theorem graph.

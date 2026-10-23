# Provenance v1: test topology and independent audit handoff

Status: proposed test setup, not an executed industrial acceptance. Authorization
remains blocked, external industrial Witness NOT_CONNECTED, C0–C6 indeterminate,
physical tests not_run and Third Obligation OPEN. The independent audit is assigned
to another agent; this document is preparation and a list of review questions.

## Three roles and two test levels

| Role | Proposed starting capacity (not a measured minimum) | Responsibility |
| --- | --- | --- |
| A: application / validator | Linux x86-64, Ubuntu 24.04 baseline; 4 vCPU, 16 GiB RAM, 60 GiB local SSD free | Pinned Lean toolchain, CPython extension, libsodium and separately qualified corrected SQLite; 2–4 worker processes on ONE local registry |
| B: external digital Witness | Separately administered host/account and disk; 2 vCPU, 4 GiB RAM, 20 GiB SSD initially | TLS1.3/mTLS, fresh authoritative reads, durable whole-head CAS, per-store ACL, independent rollback protection and recovery evidence |
| C: driver / auditor | 2 vCPU, 4 GiB RAM, 20 GiB for bounded test runs; 16 GiB RAM if also building Lean | Generate synthetic signed requests, inject controlled network/process faults, collect invocation/response histories and independent receipts |

The capacities are engineering starting budgets, not performance/OOM guarantees.
Do not buy special laboratory hardware for these software tests. A and C may share
one development host for the first regression level. B can be a separate VM for
transport tests, but co-rollbackable VMs/shared administrator credentials do not
establish independent Anti-Rollback protection. The second level requires a real
independent witness implementation and a justified persistence/anti-rollback design.
The repository supplies a CLIENT and loopback test fixture, not a qualified production
Witness server. Moving the fixture to a second machine does not qualify it.

SQLite WAL must stay on A's local filesystem, not NFS/SMB/shared network storage.
Keep WAL, SHM and the main database under the same protected directory. WAL requires
same-host shared memory; see [SQLite WAL](https://sqlite.org/wal.html).
Use WAL, synchronous=FULL, foreign_keys=ON and recursive_triggers=ON as pinned by
the adapter. Query effective PRAGMA values; do not infer success from a command
without error. FULL is an explicit durability setting, still dependent on the VFS,
OS and device: [SQLite synchronous](https://sqlite.org/pragma.html#pragma_synchronous).
A database checkpoint (WAL consolidation) and the application checkpoint digest
are distinct concepts.

## Inputs required before target acceptance

- Exact application commit, compiler/toolchain, OS/kernel/filesystem, CPU, CPython
  extension, SQLite and libsodium artifacts and SHA-256; record loaded paths too.
- A target-qualified runtime profile. Public profile.json has an EXAMPLE /opt path,
  not a deployed binary or an automatically approved profile. Do not change pins
  just to make a test pass. Rebuilding the library can change the binary hash and
  requires explicit qualification; version/source ID alone does not identify the fix.
- DNS/SAN, HTTPS port (443 suggested), server_id, external store_id, CA certificate,
  server leaf DER SHA-256, a per-store mTLS client certificate/key and a reviewed
  configuration hash delivered by a separate trusted channel. Keep keys out of Git.
- Independently specified ExpectedContext, VerificationLimits, signer/role/key registry,
  revocation list, session/policy IDs, context revision and timestamp policy.
- Controlled initial provisioning of a NEW synthetic store and externally recorded
  initial head. Never reset/re-enroll an old store to silence a mismatch.
- Witness operator evidence for atomic CAS, fresh reads, restart/failover, durable ACK,
  rollback resistance, backup/restore and ACL enforcement. A TLS probe alone is insufficient.

Open only A→B TCP HTTPS and separately controlled administrative access. C must
not hold B's administrator credential. Use independent backups and a second
administrative trust boundary; a Merkle tree/WAL rolled back with B is insufficient.
Time synchronization supports certificate validity and test correlation but does
not prove physical freshness of a signed measurement. Use monotonic timestamps
for invocation/response ordering.

## Test progression and exact pass conditions

1. On an isolated source checkout, build Lean and run the pure contract tests.
   Preserve cache and set LEAN_NUM_THREADS=1; constrain the heavy audit process to
   8 GiB memory when reproducing this project's resource profile. The host needs
   additional memory for the OS and other roles.
2. Qualify and install the exact native artifacts; runtime check must verify the
   actually mapped library. Then run ALL opt-in native tests with zero skips.
   Public hosted CI deliberately does not qualify these host-specific artifacts.
3. Exercise check-config, read-only probe and guarded inspect against B. Record
   failed pins, wrong SAN/client identity/store ACL, TLS downgrade and unavailable B.
   No fallback, automatic enrollment or reset is permitted.
4. Use the fixed synthetic four-file fixtures: valid acceptance; same/new txId
   historical repeats; signature/artifact mutation; malformed/trailing/noncanonical
   QPM; 0/exact/over limit and I/O failures; unissued challenge; context rotation.
   Verify report fields and exact logical SQL differences, not just exit status.
5. Launch 2, then 4 workers with identical and different statements. Check at most
   one NEW_ACCEPTANCE; preserve original NEW_ACCEPTANCE for the same txId and create
   HISTORICAL_RETURN only for a new matching txId. Test abort-vs-commit and context races.
6. Inject SIGKILL before/after local COMMIT, lost CAS reply, unavailable Witness,
   delays and connection termination. Resolve ambiguity through existing recovery;
   timeout does not mean rollback. Stop admission on uncertain anchor outcomes.
7. Reopen both processes, present an OLD copy of A's database while B retains its
   newer head, and require refusal. Test B's own rollback/failover policy separately;
   if independence cannot be demonstrated, leave external Anti-Rollback unqualified.
8. Prove checkpoint v1 continuity on a disposable legacy image before any planned
   production migration. Never restore a backup automatically over a current head.

All four file reads are bounded (128 KiB hard ceiling plus configured limits;
signature exactly64 bytes). Read/limit/decode rejection before registration leaves
no own writes; whole-state equality only applies without concurrent writers.
Post-registration crypto refusal can persist ABORTED without consuming the challenge.
No fault injection against an existing production registry. SIGKILL is not power-loss.
Load/latency SLOs must be specified and measured separately; this suite makes no SLO claim.

## Independent auditor checklist

Pin both public commits and the source manifest before review. Distinguish historical
private results from commands actually rerun against these public bytes/configuration.
Inspect theorem statements and hypotheses, not names alone. Audit allowed axioms
(propext, Classical.choice, Quot.sound); absence of sorryAx does not establish premises.
Trace QPM bytes → structural JSON bridge → native IO answers → report → model step →
SQLite transaction → Witness CAS. Review trust in Controller capabilities, direct Store
bypasses, target runtime/loader paths, immutable transaction identity, pinned contexts,
artifact rebinding on historical returns, read-only resolve and terminal abort fencing.

Important open review points: process/FFI correspondence is not a Lean proof; the
Ready/Prepared model is sequential, exact-content and conditional; digest collision
resistance and witness durability are external assumptions. Same statement replay
returns historical success without new consumption; a requirement to reject every
replay would disagree with the chosen contract. Native library SHA-256 is not a
publisher signature. Frozen checkpoint_profile_v1.json identifies format/state,
not the executable currently loaded. Preserve failed/OOM evidence and all non-claims.

For each finding record severity, affected commit/path/line, reproducible input,
expected/observed result, assumption violated and a regression proposal. Do not
change authorization, declare industrial acceptance or patch source during the audit
without an explicit separate work scope. Return a coverage table and unresolved items.

## Evidence packet

Collect exact commits, source/config hashes (no secrets), tool versions, effective
PRAGMAs, runtime mapping, worker IDs, monotonic call/return times, txIds, input hashes,
structured outputs, before/after logical SQL states, external head receipts and
crash injection phases. Store evidence outside the rollback domain being tested.
The private source runtime gate reported577 tests,53 Digital Brain tests and38,790
axiom declarations; these are historical source-scope results, not a fresh public
full gate. See provenance-public-validation.json for this export's actual checks.

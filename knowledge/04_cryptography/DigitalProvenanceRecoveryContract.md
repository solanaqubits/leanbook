---
id: DigitalProvenanceRecoveryContract
language: en
section: cryptography
source: Verification/DigitalProvenanceRecoveryContract.lean
source_sha256: 862e34810ad1be5c63e468e6cebc00841e902e0d92e8f1b2d11a43ba0260f3ed
novelty: not-assessed
status: reviewed
---

# Sequential replay-registry recovery

[Lean source](../../Verification/DigitalProvenanceRecoveryContract.lean).

Epsilon259, cryptography/bulletproofs-ipa. Exact-byte chronological completed log,
independent content-bound trusted prefix, prepare/persist/anchor/ack/crash/recover
state machine. The reachability invariant proves retention of all acknowledged
challenges in any accepted image. Emitted acceptance is linked to durable bytes;
after any legal tail and accepted recovery, replay is rejected using epsilon255.
The complete registry includes the reversed log and the unchanged nonempty base.

AdmissibleCrashImage is exact completed-data retention, independent of desired
acknowledgement inclusion. Incomplete writes are represented by crash before or
after the completion event. Service recovery requires this retained image; the
standalone checker permits unauthenticated suffixes and proves only prefix
non-loss. Context checks bind all nine fields, not just sessionId.

54 synthetic runtime scenarios and registry API examples accompany the proofs.
Final scoped evidence is recorded separately; no new beta or public release.
No real WAL/fsync, hardware durability, trusted-anchor implementation, cryptographic
security, concurrency, exactly-once delivery, liveness or resource bound is proved.
Authorization stays blocked; external barriers remain unchanged. Novelty not-assessed.

Independent public validation is recorded in [release v0.7.47](../../docs/release-v0.7.47.en.md). Historical development checks above do not replace public checks.

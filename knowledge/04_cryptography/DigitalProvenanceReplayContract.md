---
id: DigitalProvenanceReplayContract
language: en
section: cryptography
source: Verification/DigitalProvenanceReplayContract.lean
source_sha256: 1fe5821e1a077df10f834838f9523989e80d01c4a128462311dfdbfad357b7b8
novelty: not-assessed
status: reviewed
---

# Sequential replay protection — epsilon255

[Lean](../../Verification/DigitalProvenanceReplayContract.lean).
Hierarchy: cryptography / bulletproofs-ipa.

ChallengeRegistry fixes nine ExpectedContext fields (all except challenge) and
stores consumed raw ByteArray values in a list. Exact decidable membership uses
byte equality; hash collisions are irrelevant. Arbitrary initial lists, including
duplicates, are supported. RegistryContext fixes signer/key/role/session, policy
version, n/j/epsilon and expectedContextId.

redeemChallenge compares registry context to the independently supplied expected
context, invokes epsilon252 verifyProvenance, and checks that challenge is unused.
Acceptance prepends exactly those bytes and returns the verification report;
every refusal returns the original registry with no report. Authorization remains
blocked. Request parameters include backend, policy, limits and raw input arrays.

redeem_report_iff proves the exact CanRedeem criterion; redeem_iff expands the
verifier into canonical framing, limits and ManifestAccepted. The theorem
accepted_manifest_consumed ties consumed bytes to the accepted manifest challenge.
Validation failure, context mismatch and replay are proved refusals; all refusals
preserve the registry. Induction over the executable runRequests establishes
used-set monotonicity and context preservation. replay_after_history and
accepted_replay_after_history reject consumed bytes after arbitrary intervening
requests, even with different backend/policy parameters.

35 runtime scenarios cover success, exact insertion, replay, mixed histories,
all nine context mismatches, verification failures, distinct raw keys, initial
duplicates, empty history/challenge and blocked authorization. Separate negative
examples show that two independent stale-state calls can both accept, and rollback
can allow replay. Such operations are outside runRequests. Empty challenges are
not implicitly forbidden; issuance and entropy remain external policy requirements.
Synthetic callbacks are not cryptographic test vectors.

No concurrent atomicity, persistence, crash recovery, cryptographic implementation
security, trusted issuance, keys or clocks is established. No bound on the growing
registry's resources is proved. Actual quota-restoration composition and a trusted
atomic storage adapter are future application obligations. External service status
is not a theorem of this pure model. Novelty is not assessed. Completed verification
are recorded with this public release.


Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).

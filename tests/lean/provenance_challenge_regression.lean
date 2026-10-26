import Verification.DigitalProvenanceChallengeRegistryContract
open DigitalProvenanceManifestContract DigitalProvenanceReportContract
open DigitalProvenanceChallengeRegistryContract

-- Synthetic callbacks only; no SHA-256 or Ed25519 conformance is asserted.
private def digest (x : UInt8) : Digest256 :=
  ⟨⟨Array.replicate 32 x⟩, by simp [ByteArray.size]⟩
private def snap : ByteArray := ⟨#[1, 2, 3]⟩
private def prof : ByteArray := ⟨#[4, 5]⟩
private def key : ByteArray := ⟨Array.replicate 32 7⟩
private def sig : ByteArray := ⟨Array.replicate 64 9⟩
private def timeClaim : TimeClaim := ⟨"scale", "ticks", -3⟩
private def m : ProvenanceManifestV1 :=
  ⟨"signer", "key", "role", "session", ⟨#[10, 20]⟩, "policy",
    ⟨3, digest 1⟩, ⟨2, digest 2⟩, 3, 1, -1/2, "context", some timeClaim⟩
private def entry : PublicKeyEntry := ⟨"signer", "key", "role", "policy", key⟩
private def window : TrustedTimeWindow := ⟨"scale", "ticks", -5, 0⟩
private def ctx : ExpectedContext :=
  ⟨"context", "signer", "role", "session", "policy", 3, 1, -1/2,
    [entry], [], some m.challenge, some window⟩
private def limits : VerificationLimits := ⟨⟨4096, 128, 32⟩, 1024, 1024, 16, 16, 128⟩
private def backend : CryptoBackend :=
  ⟨fun b => .ok (if b = snap then digest 1 else if b = prof then digest 2 else if b =
    signingMessageV1 m then digest 3 else digest 4),
   fun k _ s => .ok (decide (k = key ∧ s = sig))⟩
private def good : VerificationReport :=
  ⟨.valid, .authorized, .matched, .challenge_matched, .within_trusted_window,
    .matched, .matched, .blocked⟩
private def ck : ChallengeKey := ⟨⟨"context", "session", "policy"⟩, m.challenge⟩
private def cfg : ContextConfig := ⟨ctx, limits, false⟩
private def q : Request := ⟨ck, "v1", ⟨m, sig⟩, snap, prof⟩
private def rec : ConsumedRecord := ⟨digest 3, "v1", good⟩
private def prepared (c := cfg) (req := q) : State :=
  run backend initial [.installContext req.contextVersion c, .issue req.key,
    .beginTransaction "a" req]
private def completed : State := (commitChecked backend prepared "a" q).1
private def beginAt (s : State) (tx : String) (req := q) : State :=
  (step backend s (.beginTransaction tx req)).1
private def rejected (req : Request) (c := cfg) (b := backend) : Bool :=
  decide ((commitChecked b (prepared c req) "a" req).2 = .rejected .verification_rejected)

example (crypto inputs) : (run crypto initial inputs).accepted.Nodup :=
  at_most_one_consumption crypto inputs
example (crypto s k tx is) (h : resolve s k tx = .confirmed_not_committed) :
    resolve (run crypto s is) k tx = .confirmed_not_committed := (resolve_sound crypto s k tx is
      h).1
example (crypto s tx q r) (h : (commitChecked crypto s tx q).2 = .newly_consumed r) :
    s.entries q.key = some .issued := (consume_requires_issued crypto s tx q r h).1
example (crypto cfg q r) (h : checkNew crypto cfg q = some r) :
    verifyProvenance crypto cfg.limits cfg.expected q.signed q.snapshot q.profile =
      .ok r.historicalReport := (checkNew_sound crypto cfg q r h).2.1

def main : IO Unit := do
  let changed := { q with signed := ⟨{m with j := 2}, sig⟩ }
  let revoked := {cfg with expected := {ctx with revokedKeys := [("signer", "key")]}}
  let updated := (step backend prepared (.installContext "v2" revoked)).1
  let completedUpdated := (step backend completed (.installContext "v2" revoked)).1
  let aborted := (step backend prepared (.abort "a")).1
  let missing := {q with signed := ⟨{m with claimedTime := none}, sig⟩}
  let noKey := (step backend initial (.beginTransaction "a" q)).1
  let race := beginAt prepared "b"
  let winA := (commitChecked backend race "a" q).1
  let winB := (commitChecked backend race "b" q).1
  let sameIdOther := {q with key := {ck with scope := {ck.scope with sessionId := "other"}}}
  let failedHash := {backend with sha256 := fun _ => .error .backend_failure}
  let scopeCases : List (String × ProvenanceManifestV1 × ExpectedContext) := [
    ("session", {m with sessionId := "session2"}, {ctx with expectedSessionId := "session2"}),
    ("context", {m with expectedContextId := "context2"}, {ctx with contextId := "context2"}),
    ("policy", {m with policyVersion := "policy2"},
      {ctx with expectedPolicyVersion := "policy2", keyRegistry := [{entry with policyVersion
                                                                      := "policy2"}]})]
  let scopeChecks := scopeCases.map fun (name, mm, cc) =>
    let k : ChallengeKey := ⟨scopeOf cc, mm.challenge⟩
    let req : Request := ⟨k, "independent", ⟨mm, sig⟩, snap, prof⟩
    let final := run backend completed [.installContext "independent" ⟨cc, limits, false⟩,
      .issue k, .beginTransaction "other" req, .commit "other" req]
    ("independent " ++ name, decide (final.accepted = [k, ck]))
  let cases : List (String × Bool) := [
    ("check real pure verifier result", decide (checkNew backend cfg q = some rec)),
    ("initial absent", decide (initial.entries ck = none)),
    ("unissued not unused", decide ((commitChecked backend noKey "a" q).2 = .rejected
      .challenge_not_issued)),
    ("begin required", decide ((commitChecked backend initial "a" q).2 = .rejected
      .transaction_not_started)),
    ("issuance requires context", decide ((step backend initial (.issue ck)).2 = .administrative
      false)),
    ("issuance registered", decide (prepared.entries ck = some .issued)),
    ("duplicate issue refused", decide ((step backend prepared (.issue ck)).2 = .administrative
      false)),
    ("new acceptance", decide ((commitChecked backend prepared "a" q).2 = .newly_consumed rec)),
    ("consumed value", decide (completed.entries ck = some (.consumed rec))),
    ("event recorded once", decide (completed.accepted = [ck])),
    ("consumed cannot reissue", decide ((step backend completed (.issue ck)).2 = .administrative
      false)),
    ("same tx retry", decide ((commitChecked backend completed "a" q).2 =
      .idempotent_replay_matched rec)),
    ("new tx retry", decide ((commitChecked backend (beginAt completed "b") "b" q).2 =
      .idempotent_replay_matched rec)),
    ("retry preserves log", decide ((commitChecked backend (beginAt completed "b") "b"
      q).1.accepted = [ck])),
    ("resolve new kind", decide (resolve completed ck "a" = .confirmed_committed rec
      .newAcceptance)),
    ("resolve historical kind", decide (resolve (commitChecked backend (beginAt completed "b") "b"
      q).1 ck "b" = .confirmed_committed rec .historicalReturn)),
    ("resolve missing", decide (resolve initial ck "a" = .still_indeterminate)),
    ("resolve pending", decide (resolve prepared ck "a" = .still_indeterminate)),
    ("resolve wrong key", decide (resolve completed sameIdOther.key "a" = .still_indeterminate)),
    ("abort final", decide (resolve aborted ck "a" = .confirmed_not_committed)),
    ("late commit refused", decide ((commitChecked backend aborted "a" q).2 = .rejected
      .transaction_aborted)),
    ("rebegin aborted refused", decide ((step backend aborted (.beginTransaction "a" q)).2 =
      .administrative false)),
    ("abort committed no effect", decide ((step backend completed (.abort "a")).2 = .administrative
      false)),
    ("unknown abort no finalization", decide (resolve (step backend initial (.abort "a")).1 ck "a"
      = .still_indeterminate)),
    ("context race refused", decide ((commitChecked backend updated "a" q).2 = .rejected
      .context_changed)),
    ("context refusal preserves issued", decide ((commitChecked backend updated "a" q).1.entries ck
      = some .issued)),
    ("old version cannot reactivate", decide ((step backend updated (.installContext "v1" cfg)).2 =
      .administrative false)),
    ("active version still v2", decide ((step backend updated (.installContext "v1" cfg)).1.active
      ck.scope = some "v2")),
    ("historical return after revoke", decide ((commitChecked backend completedUpdated "a" q).2 =
      .idempotent_replay_matched rec)),
    ("historical return new tx after revoke", decide ((commitChecked backend (beginAt
      completedUpdated "b") "b" q).2 = .idempotent_replay_matched rec)),
    ("same tx different message", decide ((commitChecked backend completed "a" changed).2 =
      .rejected .transaction_conflict)),
    ("same tx different key", decide ((commitChecked backend completed "a" sameIdOther).2 =
      .rejected .transaction_conflict)),
    ("pending tx conflict", decide ((commitChecked backend prepared "a" changed).2 = .rejected
      .transaction_conflict)),
    ("conflict leaves pending", decide ((commitChecked backend prepared "a" changed).1.transactions
      "a" = prepared.transactions "a")),
    ("different consumed statement", decide ((commitChecked backend (beginAt completed "b" changed)
      "b" changed).2 = .rejected .challenge_already_used)),
    ("retry snapshot byte mutation", decide ((commitChecked backend completed "a" {q with snapshot
      := ⟨#[1, 2, 4]⟩}).2 = .rejected .verification_rejected)),
    ("retry profile byte mutation", decide ((commitChecked backend completed "a" {q with profile
      := ⟨#[4, 6]⟩}).2 = .rejected .verification_rejected)),
    ("retry snapshot size", decide ((commitChecked backend completed "a" {q with snapshot
      := ⟨#[]⟩}).2 = .rejected .verification_rejected)),
    ("retry profile size", decide ((commitChecked backend completed "a" {q with profile
      := ⟨#[]⟩}).2 = .rejected .verification_rejected)),
    ("retry hash backend failure", decide ((commitChecked failedHash completed "a" q).2 = .rejected
      .verification_rejected)),
    ("race winner a", decide ((commitChecked backend race "a" q).2 = .newly_consumed rec)),
    ("race loser b historical", decide ((commitChecked backend winA "b" q).2 =
      .idempotent_replay_matched rec)),
    ("race winner b", decide ((commitChecked backend race "b" q).2 = .newly_consumed rec)),
    ("race loser a historical", decide ((commitChecked backend winB "a" q).2 =
      .idempotent_replay_matched rec)),
    ("race one event", decide ((commitChecked backend winA "b" q).1.accepted = [ck])),
    ("bad signature", rejected {q with signed := ⟨m, ⟨#[]⟩⟩}),
    ("signature false", rejected q cfg {backend with verifyEd25519 := fun _ _ _ => .ok false}),
    ("signature backend failure", rejected q cfg
      {backend with verifyEd25519 := fun _ _ _ => .error .backend_failure}),
    ("hash failure", rejected q cfg failedHash),
    ("artifact mutation new", rejected {q with snapshot := ⟨#[1, 2, 4]⟩}),
    ("revoked new", rejected q revoked),
    ("absent key", rejected q {cfg with expected := {ctx with keyRegistry := []}}),
    ("wrong parameters", rejected {q with signed := ⟨{m with j := 2}, sig⟩}),
    ("wrong signed challenge", rejected {q with signed := ⟨{m with challenge := ⟨#[99]⟩}, sig⟩}),
    ("missing time denied", rejected missing),
    ("missing time explicitly allowed", (checkNew backend {cfg with allowMissingTimestamp := true}
      missing).isSome),
    ("expired time", rejected {q with signed := ⟨{m with claimedTime := some {timeClaim with value
      := -6}}, sig⟩}),
    ("bad time window", rejected q {cfg with expected :=
      {ctx with trustedTimeWindow := some {window with minTime := 1}}}),
    ("limit refusal", rejected q {cfg with limits := {limits with maxSnapshotSizeBytes := 0}}),
    ("no active challenge", decide (checkNew backend {cfg with expected := {ctx
      with activeChallenge := none}} q = none)),
    ("loss after commit", decide (delivered true (.redemption (.newly_consumed rec)) = none ∧
      completed.entries ck = some (.consumed rec))),
    ("resolve after lost response", decide (resolve completed ck "a" = .confirmed_committed rec
      .newAcceptance)),
    ("all success statuses required", decide (reportAccepted true {good with replay
                                                                    := .not_checked} = false)),
    ("historical authorization blocked", decide (rec.historicalReport.authorization = .blocked))]
  let cases := cases ++ scopeChecks
  for (label, passed) in cases do
    unless passed do throw (IO.userError label)
  IO.println s!"PROVENANCE_CHALLENGE_OK {cases.length}"

import Verification.DigitalProvenanceRecoveryContract
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract
open DigitalProvenanceReplayContract DigitalProvenanceRecoveryContract

-- Synthetic callbacks isolate state transitions; these are not cryptographic test vectors.
private def dg : Digest256 := ⟨⟨Array.replicate 32 1⟩, by simp [ByteArray.size]⟩
private def bytes : ByteArray := ⟨#[4, 5]⟩
private def key : ByteArray := ⟨Array.replicate 32 7⟩
private def sig : ByteArray := ⟨Array.replicate 64 9⟩
private def c1 : ByteArray := ⟨#[1, 2]⟩
private def c2 : ByteArray := ⟨#[1, 2, 0]⟩
private def c3 : ByteArray := ⟨#[1, 3]⟩
private def manifest (c : ByteArray) : ProvenanceManifestV1 :=
  ⟨"signer", "key", "role", "session", c, "policy-v1",
    ⟨2, dg⟩, ⟨2, dg⟩, 3, 1, -1/2, "context", none⟩
private def backend : CryptoBackend := ⟨fun _ => dg, fun k _ s => decide (k = key ∧ s = sig)⟩
private def policy : VerificationPolicy :=
  ⟨fun signer kid => if signer = "signer" ∧ kid = "key" then some key else none,
   fun _ _ => false, fun t => decide (t = none)⟩
private def request (c : ByteArray) : RedemptionRequest :=
  ⟨⟨4096, 128, 32⟩, backend, policy, manifestContext (manifest c),
    encodeManifestV1 (manifest c), sig, bytes, bytes⟩
private def r0 : ChallengeRegistry := ⟨contextOf (request c1).expected, []⟩
private def bad : RedemptionRequest :=
  { request c1 with backend := { backend with verifyEd25519 := fun _ _ _ => false } }
private def successful (r : ChallengeRegistry) (c : ByteArray) : Bool :=
  decide ((redeemChallenge r (request c)).report = some (acceptedReport (manifest c)))


private def cycle (c : ByteArray) : List Action :=
  [.prepare (request c), .persist, .anchorCommit, .acknowledge]
private def nonempty : ChallengeRegistry := { r0 with usedChallenges := [c3, c3] }

example (b s e i r) (hr : Reachable b s)
    (hv : restoreRegistry? e (trusted b s) i = some r) :
    s.acknowledged ⊆ r.usedChallenges := crash_recovery_sound b s e i r hr hv
example (b s i) (hr : Reachable b s) (hi : AdmissibleCrashImage b s i) :
    restoreRegistry? b.context (trusted b s) i = some (registryAt b s.committed) :=
  admissible_restore b s i hr hi
example (b s a c tail e i r q) (hr : Reachable b s)
    (he : (step b s a).emitted = some c)
    (hv : restoreRegistry? e (trusted b (run b (step b s a).state tail)) i = some r)
    (hc : q.expected.challenge = c) : redeemChallenge r q = reject r :=
  emitted_replay_after_recovery b s a c tail e i r q hr he hv hc
example (b s q report) (ho : s.online = true) (hp : s.phase = .idle)
    (hv : (redeemChallenge (registryAt b s.committed) q).report = some report) :
    registryAt b (persist (prepare b s q).state).state.committed =
      (redeemChallenge (registryAt b s.committed) q).registry :=
  persist_refines_redemption b s q report ho hp hv

def main : IO Unit := do
  let start := initial nonempty
  let prepared := (prepare nonempty start (request c1)).state
  let written := (persist prepared).state
  let sealed := (anchorCommit written).state
  let acked := acknowledge sealed
  let stopped := (crash acked.state).state
  let resumed := recover nonempty nonempty.context stopped (image nonempty stopped)
  let full := run nonempty start (cycle c1 ++ cycle c2)
  let anchor : TrustedPrefix := ⟨nonempty, [c1]⟩
  let correct : RegistryImage := ⟨nonempty, [c1]⟩
  let changed : RegistryImage := ⟨nonempty, [c2]⟩
  let larger : RegistryImage := ⟨nonempty, [c2, c3]⟩
  let suffix : RegistryImage := ⟨nonempty, [c1, c2]⟩
  let cases : List (String × Bool) := [
    ("initial duplicate base retained", decide (start.acknowledged = [c3, c3])),
    ("initial exact registry", decide (registryAt nonempty [] = nonempty)),
    ("prepared has no durable data", decide (prepared.committed = [] ∧ prepared.anchor = [])),
    ("prepared not externally accepted", decide ((prepare nonempty start (request c1)).emitted =
      none)),
    ("early ack before persist refused", decide (acknowledge prepared = quiet prepared)),
    ("early anchor before persist refused", decide (anchorCommit prepared = quiet prepared)),
    ("written exact chronological entry", decide (written.committed = [c1] ∧ written.anchor = [])),
    ("written has no new ack", decide (written.acknowledged = [c3, c3])),
    ("early ack before anchor refused", decide (acknowledge written = quiet written)),
    ("persist only once", decide (persist written = quiet written)),
    ("anchor exact content", decide (sealed.anchor = [c1])),
    ("anchor does not emit ack", decide ((anchorCommit written).emitted = none)),
    ("external ack exact", decide (acked.emitted = some c1)),
    ("ack records ghost history", decide (acked.state.acknowledged = [c1, c3, c3])),
    ("duplicate ack prevented", decide (acknowledge acked.state = quiet acked.state)),
    ("crash clears volatile only", decide (stopped.pending = none ∧ stopped.online = false ∧
      stopped.committed = [c1] ∧ stopped.anchor = [c1] ∧ stopped.acknowledged = [c1, c3, c3])),
    ("offline cannot prepare", decide (prepare nonempty stopped (request c2) = quiet stopped)),
    ("offline cannot persist", decide (persist stopped = quiet stopped)),
    ("offline cannot emit", decide (acknowledge stopped = quiet stopped)),
    ("admissible recovery resumes", decide (resumed.state.online = true)),
    ("restore exact base plus reversed log", decide
      (restoreRegistry? nonempty.context (trusted nonempty full) (image nonempty full) =
        some ⟨nonempty.context, [c2, c1, c3, c3]⟩)),
    ("recovered replay refused", decide
      (redeemChallenge (registryAt nonempty resumed.state.committed) (request c1) =
        reject (registryAt nonempty resumed.state.committed))),
    ("retry lost response still refused", decide
      (redeemChallenge (registryAt nonempty written.committed) (request c1) =
        reject (registryAt nonempty written.committed))),
    ("exact prefix accepted", decide (restoreRegistry? nonempty.context anchor correct =
      some ⟨nonempty.context, [c1, c3, c3]⟩)),
    ("truncation rejected", decide (restoreRegistry? nonempty.context anchor ⟨nonempty, []⟩ =
      none)),
    ("same version different bytes rejected", decide
      (changed.entries.length = anchor.entries.length ∧ restoreRegistry? nonempty.context anchor
        changed = none)),
    ("higher version different bytes rejected", decide
      (larger.entries.length > anchor.entries.length ∧ restoreRegistry? nonempty.context anchor
        larger = none)),
    ("numeric-only mutation would accept", decide (larger.entries.length ≥ anchor.entries.length)),
    ("suffix inclusion not provenance", decide (restoreRegistry? nonempty.context anchor suffix =
      some ⟨nonempty.context, [c2, c1, c3, c3]⟩)),
    ("service rejects unauthenticated suffix", decide
      (recover nonempty nonempty.context stopped suffix = quiet stopped)),
    ("wrong base rejected", decide (restoreRegistry? nonempty.context anchor ⟨r0, [c1]⟩ = none)),
    ("failure stays offline", decide ((recover nonempty nonempty.context stopped
      changed).state.online = false)),
    ("validation refusal unchanged", decide (prepare nonempty start bad = quiet start)),
    ("already used bytes unchanged", decide (prepare nonempty start (request c3) = quiet start)),
    ("busy prepare refused", decide (prepare nonempty prepared (request c2) = quiet prepared)),
    ("empty challenge allowed by synthetic policy", decide
      ((run r0 (initial r0) (cycle ⟨#[]⟩)).acknowledged = [⟨#[]⟩])),
    ("both outcomes blocked", decide (acked.authorization = .blocked ∧ resumed.authorization =
      .blocked)),
    -- Excluded mutations, not operations of this state machine.
    ("empty fallback loses protection", successful { nonempty with usedChallenges := [] } c3),
    ("early-ack mutation loses challenge on crash", decide
      (c1 ∉ (registryAt nonempty (crash prepared).state.committed).usedChallenges)),
    ("repeated crash recovery retains data", decide
      ((recover nonempty nonempty.context (crash resumed.state).state correct).state.committed =
        [c1]))]
  let contexts : List RegistryContext := [
    { nonempty.context with signerId := "other" }, { nonempty.context with keyId := "other" },
    { nonempty.context with roleId := "other" }, { nonempty.context with sessionId := "other" },
    { nonempty.context with policyVersion := "other" }, { nonempty.context with n := 4 },
    { nonempty.context with j := 2 }, { nonempty.context with epsilon := 0 },
    { nonempty.context with expectedContextId := "other" }]
  for (label, ok) in cases do
    unless ok do throw (IO.userError label)
  for ctx in contexts do
    unless restoreRegistry? ctx anchor correct = none ∧
        recover nonempty ctx stopped correct = quiet stopped do
      throw (IO.userError "full context binding")
  -- Independent expected journal/ack values at each crash boundary.
  for k in List.range 5 do
    let s := run nonempty start ((cycle c1).take k)
    let dead := (crash s).state
    let back := (recover nonempty nonempty.context dead (image nonempty dead)).state
    let log := if k < 2 then [] else [c1]
    let acks := if k < 4 then [c3, c3] else [c1, c3, c3]
    unless dead.committed = log ∧ back.committed = log ∧ back.online = true ∧
        back.acknowledged = acks do throw (IO.userError s!"crash boundary {k}")
  IO.println s!"PROVENANCE_RECOVERY_OK {cases.length + contexts.length + 5}"

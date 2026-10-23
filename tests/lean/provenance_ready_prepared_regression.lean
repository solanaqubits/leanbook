import Verification.DigitalProvenanceReadyPreparedContract
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract
open DigitalProvenanceReplayContract DigitalProvenanceReadyPreparedContract
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



private def p1 (b : ChallengeRegistry) (c : ByteArray) : State :=
  { initial b with pending := some c, phase := .planned }
private def p2 (b : ChallengeRegistry) (c : ByteArray) : State :=
  { p1 b c with head := .prepared 0 [] [c], phase := .witnessed }
private def p3 (b : ChallengeRegistry) (c : ByteArray) : State :=
  { p2 b c with completed := [c], phase := .durable }
private def p4 (b : ChallengeRegistry) (c : ByteArray) : State :=
  { p3 b c with head := .ready 1 [c], phase := .sealed }
private def p5 (b : ChallengeRegistry) (c : ByteArray) : State :=
  { p4 b c with pending := none, phase := .idle, acknowledged := c :: b.usedChallenges }
private def dead (s : State) : State :=
  { s with pending := none, phase := .idle, online := false }

-- A successful six-state execution is derivable from the actual validator premise;
-- the correspondence is not vacuous because all transitions are forbidden.
private theorem full_cycle (b q report)
    (hv : (redeemChallenge (DigitalProvenanceRecoveryContract.registryAt b []) q).report = some report) :
    Execution b (initial b) [none, none, none, none, some q.expected.challenge]
      (p5 b q.expected.challenge) := by
  apply Execution.cons (Step.prepare (initial b) q report 0 rfl rfl rfl hv)
  apply Execution.cons (Step.witnessPrepare (p1 b q.expected.challenge) 0 q.expected.challenge rfl rfl rfl rfl)
  apply Execution.cons (Step.sqlCommit (p2 b q.expected.challenge) 0 q.expected.challenge rfl rfl rfl rfl)
  apply Execution.cons (Step.finalize (p3 b q.expected.challenge) 0 [] rfl rfl rfl)
  apply Execution.cons (Step.acknowledge (p4 b q.expected.challenge) 1 q.expected.challenge rfl rfl rfl rfl (by simp [p4, p3]))
  exact Execution.nil _

example (b q report) (hv : (redeemChallenge (DigitalProvenanceRecoveryContract.registryAt b []) q).report = some report) :
    Reachable b (dead (p5 b q.expected.challenge)) := by
  refine ⟨[none, none, none, none, some q.expected.challenge, none], ?_⟩
  have append_crash : ∀ s os t, Execution b s os t →
      Execution b s (os ++ [none]) (dead t) := by
    intro s os t hx
    induction hx with
    | nil s => exact Execution.cons (Step.crash s) (Execution.nil _)
    | cons hs hx ih => exact Execution.cons hs ih
  exact append_crash _ _ _ (full_cycle b q report hv)

example (b c) : Step b (dead (p3 b c)) none
    { dead (p3 b c) with head := .ready 1 [c] } :=
  Step.recoverPrepared _ 0 [] rfl rfl

example (b c) : Step b (dead (p4 b c)) none
    { dead (p4 b c) with online := true, phase := .idle, pending := none } :=
  Step.recoverReady _ 1 rfl rfl

example (b s os t) (hx : Execution b s os t) (a) (h : Related b s a) :
    ∃ actions, Related b t (abstractTrace b a actions).1 ∧
      (abstractTrace b a actions).2 = os.flatMap Option.toList :=
  execution_simulation b s os t hx a h

example (b s i r q) (hs : Reachable b s) (hv : restoreCandidate? b s i = some r)
    (hc : q.expected.challenge ∈ s.acknowledged) : redeemChallenge r q = reject r :=
  recovered_replay_rejected b s i r q hs hv hc

def main : IO Unit := do
  let b := { r0 with usedChallenges := [c3, c3] }
  let good : DigitalProvenanceRecoveryContract.RegistryImage := ⟨b, [c1]⟩
  let stop := dead (p5 b c1)
  let expected := DigitalProvenanceRecoveryContract.registryAt b [c1]
  let unsealed := dead (p3 b c1)
  let finalized := { unsealed with head := Head.ready 1 [c1] }
  let badBase := { b with usedChallenges := [] }
  let badContext := { b with context := { b.context with sessionId := "other" } }
  let cases : List (String × Bool) := [
    ("fixture accepted", successful b c1),
    ("fixture invalid signature rejected", decide ((redeemChallenge b bad).report = none)),
    ("successful restoration exact", decide (restoreCandidate? b stop good = some expected)),
    ("base duplicates preserved", decide (expected.usedChallenges = [c1,c3,c3])),
    ("replay refused", decide (redeemChallenge expected (request c1) = reject expected)),
    ("distinct raw bytes not conflated", successful expected c2),
    ("prepared head fails closed", decide (restoreCandidate? b unsealed good = none)),
    ("recovery finalization permits exact image", decide (restoreCandidate? b finalized good = some expected)),
    ("online recovery refused", decide (restoreCandidate? b (p5 b c1) good = none)),
    ("lost completed entry rejected", decide (restoreCandidate? b stop ⟨b,[]⟩ = none)),
    ("same length wrong bytes rejected", decide (restoreCandidate? b stop ⟨b,[c2]⟩ = none)),
    ("untrusted suffix rejected", decide (restoreCandidate? b stop ⟨b,[c1,c2]⟩ = none)),
    ("base mutation rejected", decide (restoreCandidate? b stop ⟨badBase,[c1]⟩ = none)),
    ("context mutation rejected", decide (restoreCandidate? b stop ⟨badContext,[c1]⟩ = none)),
    ("stale head content rejected", decide (restoreCandidate? b {stop with head := .ready 0 []} good = none)),
    ("large epoch cannot mask content change", decide (restoreCandidate? b {stop with head := .ready 1000 [c2]} good = none)),
    ("epoch alone deliberately not freshness", decide (restoreCandidate? b {stop with head := .ready 0 [c1]} good = some expected)),
    ("empty pending retains completed data", decide (finalized.pending = none ∧ finalized.completed = [c1])),
    ("lost response need not be acknowledged", decide (finalized.acknowledged = [c3,c3])),
    ("lost response challenge still consumed", decide (redeemChallenge expected (request c1) = reject expected)),
    ("early ack mutation is outside protocol and loses protection", decide (c1 ∉ (DigitalProvenanceRecoveryContract.registryAt b []).usedChallenges)),
    ("all abstract output statuses blocked", decide ((DigitalProvenanceRecoveryContract.acknowledge (DigitalProvenanceRecoveryContract.initial b)).authorization = .blocked)),
    ("empty trace is identity", decide (abstractTrace b (DigitalProvenanceRecoveryContract.initial b) [] = (DigitalProvenanceRecoveryContract.initial b, []))),
    ("abstract full trace emits once", decide ((abstractTrace b (DigitalProvenanceRecoveryContract.initial b)
      [.prepare (request c1),.persist,.anchorCommit,.acknowledge,.crash]).2 = [c1]))]
  for (label, ok) in cases do
    unless ok do throw (IO.userError label)
  -- Before SQL completion the Prepared head cannot be reconciled from this model;
  -- after completion it requires explicit recovery finalization before acceptance.
  let states := [initial b, p1 b c1, p2 b c1, p3 b c1, p4 b c1, p5 b c1]
  for (s,k) in states.zipIdx do
    let stopped := dead s
    let log := if k < 3 then [] else [c1]
    let ack := if k < 5 then [c3,c3] else [c1,c3,c3]
    unless stopped.completed = log ∧ stopped.acknowledged = ack do
      throw (IO.userError s!"crash retention {k}")
    let result := restoreCandidate? b stopped ⟨b,log⟩
    let wanted := if k = 2 ∨ k = 3 then none else some (DigitalProvenanceRecoveryContract.registryAt b log)
    unless result = wanted do throw (IO.userError s!"crash decision {k}")
  IO.println s!"READY_PREPARED_OK {cases.length + states.length}"

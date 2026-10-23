import Verification.DigitalProvenanceReplayContract
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract
open DigitalProvenanceReplayContract

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

example (r qs q) (h : q.expected.challenge ∈ r.usedChallenges) :
    redeemChallenge (runRequests r qs) q = reject (runRequests r qs) :=
  replay_after_history r qs q h
example (r q) (h : checkedReport q = none) :
    redeemChallenge r q = reject r := validation_failure_preserves r q h
example (r q) (h : (redeemChallenge r q).report = none) :
    (redeemChallenge r q).registry = r := rejected_registry_unchanged r q h
example (r qs) : (runRequests r qs).context = r.context := run_context_preserved r qs
example (r qs) : r.usedChallenges ⊆ (runRequests r qs).usedChallenges := run_used_monotone r qs
example (r q m) (h : (redeemChallenge r q).report = some (acceptedReport m)) :
    m.challenge ∈ (redeemChallenge r q).registry.usedChallenges := accepted_manifest_consumed r q m h
example (r q rp qs later) (h : (redeemChallenge r q).report = some rp)
    (hc : later.expected.challenge = q.expected.challenge) :
    redeemChallenge (runRequests (redeemChallenge r q).registry qs) later =
      reject (runRequests (redeemChallenge r q).registry qs) :=
  accepted_replay_after_history r q rp qs later h hc

def main : IO Unit := do
  let first := redeemChallenge r0 (request c1)
  let r1 := first.registry
  let history := [bad, request c2, request c2, request c3, request c1]
  let final := runRequests r1 history
  let contexts : List RegistryContext := [
    { r0.context with signerId := "other" }, { r0.context with keyId := "other" },
    { r0.context with roleId := "other" }, { r0.context with sessionId := "other" },
    { r0.context with policyVersion := "other" }, { r0.context with n := 4 },
    { r0.context with j := 2 }, { r0.context with epsilon := 0 },
    { r0.context with expectedContextId := "other" }]
  let refusals : List RedemptionRequest := [bad,
    { request c1 with frame := ⟨#[]⟩ },
    { request c1 with frame := encodeManifestV1 (manifest c1) ++ ⟨#[0]⟩ },
    { request c1 with policy := { policy with lookupKey := fun _ _ => none } },
    { request c1 with policy := { policy with revoked := fun _ _ => true } },
    { request c1 with policy := { policy with acceptsTime := fun _ => false } },
    { request c1 with signature := ⟨#[9]⟩ },
    { request c1 with snapshot := ⟨#[4]⟩ },
    { request c1 with profile := ⟨#[5]⟩ },
    { request c1 with expected := (request c2).expected }]
  let cases : List (String × Bool) := [
    ("accept once", successful r0 c1),
    ("exact insertion", decide (r1.usedChallenges = [c1] ∧ r1.context = r0.context)),
    ("immediate replay", decide (redeemChallenge r1 (request c1) = reject r1)),
    ("different byte length accepted", successful r1 c2),
    ("different bytes accepted", successful r1 c3),
    ("empty history", decide (runRequests r1 [] = r1)),
    ("history exact state", decide (final = ⟨r0.context, [c3, c2, c1]⟩)),
    ("replay after mixed history", decide (redeemChallenge final (request c1) = reject final)),
    ("duplicate initial entries still reject", decide
      (redeemChallenge { r0 with usedChallenges := [c1, c1] } (request c1) =
        reject { r0 with usedChallenges := [c1, c1] })),
    ("failure keeps nonempty registry", decide (redeemChallenge r1 bad = reject r1)),
    ("empty challenge is not implicitly forbidden", successful r0 ⟨#[]⟩),
    ("empty challenge replay", decide
      (let rr := (redeemChallenge r0 (request ⟨#[]⟩)).registry
       redeemChallenge rr (request ⟨#[]⟩) = reject rr)),
    ("success authorization blocked", decide (first.authorization = .blocked)),
    ("refusal authorization blocked", decide ((redeemChallenge r1 bad).authorization = .blocked)),
    -- These demonstrate excluded operations; neither is a legal runRequests history.
    ("two stale readers can each accept", decide
      ((redeemChallenge r0 (request c1)).report.isSome ∧
       (redeemChallenge r0 (request c1)).report.isSome)),
    ("rollback outside model can accept", successful { r1 with usedChallenges := [] } c1)]
  for (label, passed) in cases do
    unless passed do throw (IO.userError label)
  for ctx in contexts do
    let registry := { r1 with context := ctx }
    unless redeemChallenge registry (request c2) = reject registry do
      throw (IO.userError "registry context mismatch")
  for q in refusals do
    unless redeemChallenge r0 q = reject r0 do throw (IO.userError "validation refusal")
  IO.println s!"PROVENANCE_REPLAY_OK {cases.length + contexts.length + refusals.length}"

import tools.provenance_native.Adapter
import Lean
open Lean ProvenanceNative DigitalProvenanceManifestContract DigitalProvenanceReportContract

private def fromHex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [:chars.size / 2] do
    let digit (c : Char) := c.toNat - (if c ≤ '9' then 48 else 87)
    out := out.push (UInt8.ofNat (digit chars[2*i]! * 16 + digit chars[2*i+1]!))
  return out

private def parseIO {α} (x : Except String α) : IO α :=
  match x with | .ok a => pure a | .error e => throw (IO.userError e)
private def ensure (label : String) (p : Bool) : IO Unit :=
  unless p do throw (IO.userError label)
private def digest (b : ByteArray) : IO Digest256 :=
  if h : b.size = 32 then pure ⟨b,h⟩ else throw (IO.userError "digest length")

def main (args : List String) : IO Unit := do
  if args.length ≠ 3 then throw (IO.userError "library version fixture.json")
  let assertions ← IO.mkRef (0 : Nat)
  let check (label : String) (p : Bool) : IO Unit := do
    ensure label p
    assertions.modify (· + 1)
  let f ← parseIO (Json.parse (← IO.FS.readFile args[2]!))
  let field (name : String) := do return fromHex (← parseIO (f.getObjValAs? String name))
  let key ← field "public_key"
  let sig ← field "signature"
  let snapshot ← field "snapshot"
  let profile ← field "profile"
  let snapDigest ← digest (← field "snapshot_digest")
  let profDigest ← digest (← field "profile_digest")
  let m : ProvenanceManifestV1 := ⟨"fixture-signer", "rfc8032-key1", "quota-auditor",
    "native-test-session", ⟨#[16,32,48]⟩, "native-profile-v1", ⟨3,snapDigest⟩,
    ⟨2,profDigest⟩, 3, 1, -1/2, "native-context", some ⟨"test-clock","ticks",-3⟩⟩
  let expected : ExpectedContext := ⟨"native-context","fixture-signer","quota-auditor",
    "native-test-session","native-profile-v1",3,1,-1/2,
    [⟨"fixture-signer","rfc8032-key1","quota-auditor","native-profile-v1",key⟩],[],
    some m.challenge, some ⟨"test-clock","ticks",-5,0⟩⟩
  let limits : VerificationLimits := ⟨⟨4096,128,32⟩,1024,1024,16,16,128⟩
  let native := nativeBackend ⟨args[0]!,args[1]!⟩
  let good : VerificationReport := ⟨.valid,.authorized,.matched,.challenge_matched,
    .within_trusted_window,.matched,.matched,.blocked⟩
  check "independent fixture message equals exact Lean message" (signingMessageV1 m == (← field "message"))
  -- Observe the actual IO request sequence, not just a computed planned list.
  let calls ← IO.mkRef ([] : List CryptoRequest)
  let tracked : IOBackend := {
    sha256 := fun bytes => do
      calls.modify (· ++ [.hash bytes])
      native.sha256 bytes
    verifyEd25519 := fun k msg signature => do
      calls.modify (· ++ [.verify ⟨k,msg,signature⟩])
      native.verifyEd25519 k msg signature }
  let runCase (label : String) (ctx := expected) (mm := m) (signature := sig)
      (x := snapshot) (y := profile) (b := tracked) (want := good) : IO Unit := do
    calls.set []
    match ← verifyProvenanceIO b limits ctx ⟨mm,signature⟩ x y with
    | .error _ => throw (IO.userError (label ++ ": preflight"))
    | .ok e =>
      check (label ++ ": report") (decide (e.report = want))
      check (label ++ ": conformance") (conforms (planVerification ctx ⟨mm,signature⟩ x y) e)
  runCase "native positive"
  check "actual request order and bytes" (decide ((← calls.get) =
    [.verify ⟨key,signingMessageV1 m,sig⟩,.hash snapshot,.hash profile]))
  runCase "changed manifest" (mm := {m with sessionId := "tampered"})
    (want := {good with signature := .invalid_signature, contextBinding := .session_mismatch})
  runCase "bad artifact" (x := ⟨#[1,2,4]⟩) (want := {good with snapshotBinding := .digest_mismatch})
  runCase "bad size" (x := ⟨#[]⟩) (want := {good with snapshotBinding := .size_mismatch})
  check "no IO hash for wrong size" (decide ((← calls.get) =
    [.verify ⟨key,signingMessageV1 m,sig⟩,.hash profile]))
  runCase "revoked" (ctx := {expected with revokedKeys := [("fixture-signer","rfc8032-key1")]})
    (want := {good with signature := .not_checked, keyAuthorization := .revoked_key})
  check "no revoked signature IO" (decide ((← calls.get) = [.hash snapshot,.hash profile]))
  runCase "short signature" (signature := ⟨#[]⟩) (want := {good with signature := .malformed_signature})
  check "no malformed signature IO" (decide ((← calls.get) = [.hash snapshot,.hash profile]))
  runCase "changed challenge" (ctx := {expected with activeChallenge := some ⟨#[]⟩})
    (want := {good with replay := .challenge_mismatch})
  runCase "expired policy window" (ctx := {expected with trustedTimeWindow := some ⟨"test-clock","ticks",0,5⟩})
    (want := {good with freshness := .expired})
  let missing := nativeBackend ⟨"/nonexistent/provenance-library.so",args[1]!⟩
  runCase "missing library" (b := missing) (want := { good with
      signature := .crypto_backend_failure
      snapshotBinding := .crypto_backend_failure
      profileBinding := .crypto_backend_failure })
  let throwing : IOBackend := ⟨fun _ => throw (IO.userError "injected hash failure"),
    fun _ _ _ => throw (IO.userError "injected verify failure")⟩
  runCase "IO exception mapping" (b := throwing) (want := { good with
      signature := .crypto_backend_failure
      snapshotBinding := .crypto_backend_failure
      profileBinding := .crypto_backend_failure })
  calls.set []
  let refused ← verifyProvenanceIO tracked {limits with maxSnapshotSizeBytes := 0}
    expected ⟨m,sig⟩ snapshot profile
  check "limit refusal" (match refused with | .error .limit_exceeded => true | _ => false)
  check "zero observed IO requests on refusal" ((← calls.get).isEmpty)
  -- Two same-byte hash requests must have identical answers to admit a pure model.
  let counter ← IO.mkRef (0 : Nat)
  let inconsistent : IOBackend := {native with sha256 := fun _ => do
    let n ← counter.get
    counter.modify (· + 1)
    return .ok (if n = 0 then snapDigest else profDigest) }
  let p := planVerification expected ⟨m,sig⟩ snapshot snapshot
  -- Force equal requested bytes while preserving distinct declared digests.
  let p := {p with profileRequest := some snapshot}
  let e ← execute inconsistent p
  check "inconsistent duplicate request responses rejected by mapping" (!conforms p e)
  IO.println s!"NATIVE_INTEGRATION_OK {← assertions.get}"

import tools.provenance_native.Adapter
import Lean
open Lean ProvenanceNative

def unhex (s : String) : Except String ByteArray := do
  if s.utf8ByteSize % 2 ≠ 0 then throw "odd hex"
  let chars := s.toList.toArray
  let mut result := ByteArray.empty
  for i in [:chars.size / 2] do
    let a := chars[2*i]!
    let b := chars[2*i+1]!
    if !a.isHexDigit || !b.isHexDigit then throw "invalid hex"
    result := result.push (UInt8.ofNat (a.toNat - (if a ≤ '9' then 48 else if a ≤ 'F' then 55 else 87)) * 16 +
      UInt8.ofNat (b.toNat - (if b ≤ '9' then 48 else if b ≤ 'F' then 55 else 87)))
  return result

def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap (fun v =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[v.toNat / 16]!, digits[v.toNat % 16]!]))

def requireParsed {α} (v : Except String α) : IO α :=
  match v with | .ok x => pure x | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  if args.length ≠ 3 then throw (IO.userError "library version cases.json")
  let cases ← requireParsed ((← requireParsed (Json.parse (← IO.FS.readFile args[2]!))).getArr?)
  for c in cases do
    let get (k : String) := requireParsed (c.getObjValAs? String k)
    let id ← get "id"
    let config : Config := ⟨(c.getObjValAs? String "library").toOption.getD args[0]!,
      (c.getObjValAs? String "version").toOption.getD args[1]!⟩
    let backend := nativeBackend config
    let message ← requireParsed (unhex (← get "message"))
    let mut result := ""
    let mut digest := ""
    if (← get "operation") = "hash" then
      match ← backend.sha256 message with
      | .ok d => result := "ok"; digest := hex d.bytes
      | .error _ => result := "backend_failure"
    else
      let key ← requireParsed (unhex (← get "key"))
      let sig ← requireParsed (unhex (← get "signature"))
      let answer ← if (← get "operation") = "raw_verify" then do
        let rc ← rawVerify config.libraryPath config.expectedVersion key message sig
        pure (if rc = 1 then Except.ok true else if rc = 0 then .ok false
          else .error DigitalProvenanceReportContract.CryptoError.backend_failure)
        else backend.verifyEd25519 key message sig
      match answer with
      | .ok true => result := "ok_true"
      | .ok false => result := "ok_false"
      | .error _ => result := "backend_failure"
    IO.println (Json.mkObj [("id", toJson id), ("result", toJson result), ("digest",toJson digest)]).compress

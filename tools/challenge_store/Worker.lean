import tools.challenge_store.FileManifest
open Lean ChallengeStore DigitalProvenanceManifestContract
open DigitalProvenanceChallengeRegistryContract

def respond (backend : ProvenanceNative.IOBackend) (j : Json) : IO Json := do
  if let .ok raw := j.getObjVal? "decodeManifest" then
    let i : FileManifestInput ← IO.ofExcept (fromJson? raw)
    return decodeFileManifest i
  if let .ok raw := j.getObjVal? "checkManifestBridge" then
    let i : ManifestBridgeInput ← IO.ofExcept (fromJson? raw)
    return toJson (checkManifestBridge i)
  if let .ok raw := j.getObjVal? "fileRequestFits" then
    let i : FileRequestInput ← IO.ofExcept (fromJson? raw)
    return toJson (fileRequestFits i)
  if let .ok raw := j.getObjVal? "validateImage" then
    let image : Image ← IO.ofExcept (fromJson? raw)
    for (key, entry) in image.entries do
      if let .consumed r := entry then
        let some cfg := image.state.contexts r.pinnedContextVersion |
          throw (IO.userError "missing pinned context")
        if keyOf cfg.expected != some key ||
            !reportAccepted cfg.allowMissingTimestamp r.historicalReport then
          throw (IO.userError "invalid consumed record")
    for (sc, v) in image.active do
      let some cfg := image.state.contexts v | throw (IO.userError "missing active context")
      if scopeOf cfg.expected != sc then throw (IO.userError "active scope mismatch")
    return toJson image
  if let .ok qj := j.getObjVal? "binding" then
    let q : Request ← IO.ofExcept (fromJson? qj)
    return toJson (bindingOf q)
  if let .ok cj := j.getObjVal? "context" then
    let c : ContextConfig ← IO.ofExcept (fromJson? cj)
    return toJson c
  let c : ChallengeStore.Command ← IO.ofExcept (fromJson? j)
  let crypto ← collect backend c.image.state c.input
  let (s, out) := step crypto c.image.state c.input
  return Json.mkObj [("image", toJson (materialize c.image c.input s)), ("output", toJson out)]

def main (args : List String) : IO Unit := do
  let [path, version] := args | throw (IO.userError "library path and version required")
  let backend := ProvenanceNative.nativeBackend ⟨path, version⟩
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let answer ← try
      let j ← IO.ofExcept (Json.parse line)
      pure (Json.mkObj [("ok", ← respond backend j)])
      catch e => pure (Json.mkObj [("error", toJson e.toString)])
    stdout.putStrLn answer.compress
    stdout.flush

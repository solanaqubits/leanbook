-- Appended verbatim to tools/quota_snapshot_reader.lean by the Python harness.
-- The production definitions are unchanged; #eval runs callback/fault tests.
namespace QuotaSnapshotReaderTests
open QuotaSnapshotReader
open CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaSnapshotContract

private def check (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

private def source (data : ByteArray) (short : Nat) :
    IO ((USize → IO ByteArray) × IO.Ref Nat × IO.Ref (List Nat)) := do
  let offset ← IO.mkRef 0
  let calls ← IO.mkRef ([] : List Nat)
  let read : USize → IO ByteArray := fun request => do
    calls.modify (request.toNat :: ·)
    let pos ← offset.get
    let n := min request.toNat short
    let part := data.extract pos (pos + n)
    offset.set (pos + part.size)
    pure part
  pure (read, offset, calls)

private def rawCase (limit length short : Nat) : IO Unit := do
  let data : ByteArray := ⟨Array.replicate length 0x51⟩
  let (read, offset, calls) ← source data short
  let result ← readBoundedWith read limit
  match result with
  | .ok bytes => check (length ≤ limit && bytes == data) "bounded payload mismatch"
  | .error e => check (length > limit && e == .tooLarge) "incorrect overflow status"
  let consumed ← offset.get
  check (consumed ≤ limit + 1) "excessive probe consumption"
  check (consumed == min length (limit + 1)) "incorrect consumed bytes"
  check ((← calls.get).all (fun n => 0 < n && n ≤ chunkSize)) "bad read request"

private def run : IO Unit := do
  let mut cases := 0
  for limit in [0, 1, 5, 6, 65535, 65536, 65537] do
    for length in [0, limit, limit + 1, limit + 257] do
      rawCase limit length 65536
      cases := cases + 1
  for short in [1, 2, 3, 7] do
    rawCase 19 19 short
    rawCase 19 20 short
    cases := cases + 2
  let snapshot : QuotaCursorSnapshot := ⟨128, [0, 1/2, -2/3]⟩
  let bytes := encodeV1 snapshot
  for short in [1, 2, 65536] do
    let (read, _, _) ← source bytes short
    match ← readSnapshotWith read ⟨bytes.size, 128, 3⟩ with
    | .ok result =>
      check (result.snapshot == snapshot && result.bytesRead == bytes.size)
        "decode forwarding mismatch"
    | .error e => throw (IO.userError s!"valid decode failed: {repr e}")
    cases := cases + 1
  let (read, _, _) ← source (bytes.push 0) 2
  match ← readSnapshotWith read ⟨bytes.size + 1, 128, 3⟩ with
  | .error .invalidFormat => pure ()
  | _ => throw (IO.userError "trailing byte accepted")
  cases := cases + 1
  let (read, _, _) ← source bytes 2
  match ← readSnapshotWith read ⟨bytes.size, 127, 3⟩ with
  | .error .invalidFormat => pure ()
  | _ => throw (IO.userError "bound guard bypassed")
  cases := cases + 1
  let (read, _, _) ← source ByteArray.empty 1
  match ← readSnapshotWith read ⟨0, 0, 0⟩ with
  | .error .invalidFormat => pure ()
  | _ => throw (IO.userError "empty input accepted")
  cases := cases + 1
  match ← readBoundedWith (fun n => pure ⟨Array.replicate (n.toNat + 1) 0⟩) 7 with
  | .error .sourceContract => pure ()
  | _ => throw (IO.userError "over-returning source not rejected")
  cases := cases + 1
  match ← readBoundedWith (fun _ => throw (IO.userError "injected")) 7 with
  | .error (.ioError "read" msg) => check (msg.contains "injected") "lost IO diagnostic"
  | _ => throw (IO.userError "read exception not preserved")
  cases := cases + 1
  let seen ← IO.mkRef false
  let read : USize → IO ByteArray := fun _ => do
    if ← seen.get then throw (IO.userError "after partial read")
    seen.set true
    pure bytes
  match ← readSnapshotWith read ⟨bytes.size, 128, 3⟩ with
  | .error (.ioError "read" _) => pure ()
  | _ => throw (IO.userError "decoded before confirming EOF")
  cases := cases + 1
  IO.println s!"QUOTA_READER_OK {cases}"
end QuotaSnapshotReaderTests
#eval QuotaSnapshotReaderTests.run

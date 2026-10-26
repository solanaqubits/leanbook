import Verification.CryptoHiddenScalarQuotaCodecContract

/-! Executable IO adapter, not a formal model of the filesystem or Lean runtime.
No unbounded readBinFile, no stat-based acceptance and no mathematical restoration. -/
namespace QuotaSnapshotReader
open CryptoHiddenScalarQuotaCodecContract
open CryptoHiddenScalarQuotaSnapshotContract

inductive ReadError where
  | tooLarge
  | invalidFormat
  | ioError (stage message : String)
  | sourceContract
  | exhausted
  deriving Repr, BEq

/-- Every request is at most 64 KiB, including the one-byte over-limit probe. -/
def chunkSize : Nat := 65536

private def readLoop (read : USize → IO ByteArray) :
    Nat → Nat → ByteArray → IO (Except ReadError ByteArray)
  | 0, _, _ => pure (.error .exhausted)
  | fuel + 1, remaining, acc => do
    let request := min chunkSize (remaining + 1)
    let part ← read (USize.ofNat request)
    if part.size > request then return .error .sourceContract
    if part.isEmpty then return .ok acc
    if part.size > remaining then return .error .tooLarge
    readLoop read fuel (remaining - part.size) (acc ++ part)

/-- Empty reads mean EOF. Short nonempty reads continue. Assumes the callback
honors its request; detects violations but cannot undo callback allocations. -/
def readBoundedWith (read : USize → IO ByteArray) (maxBytes : Nat) :
    IO (Except ReadError ByteArray) := do
  try
    readLoop read (maxBytes + 1) maxBytes ByteArray.empty
  catch e => return .error (.ioError "read" e.toString)

structure LoadedSnapshot where
  bytesRead : Nat
  snapshot : QuotaCursorSnapshot
  deriving Repr

/-- Decode exactly the accumulated bytes only after EOF; no second file read. -/
def readSnapshotWith (read : USize → IO ByteArray) (limits : FitsLimits) :
    IO (Except ReadError LoadedSnapshot) := do
  match ← readBoundedWith read limits.maxSizeBytes with
  | .error e => return .error e
  | .ok bytes =>
    match strictDecode limits bytes with
    | none => return .error .invalidFormat
    | some snapshot => return .ok ⟨bytes.size, snapshot⟩

/-- Opens read-only. The handle does not escape the callback. Runtime handle
release is not a crash-durability guarantee or a filesystem snapshot protocol. -/
def readSnapshotFile (path : System.FilePath) (limits : FitsLimits) :
    IO (Except ReadError LoadedSnapshot) := do
  try
    IO.FS.withFile path .read fun h => readSnapshotWith h.read limits
  catch e => return .error (.ioError "open" e.toString)

def errorCode : ReadError → String
  | .tooLarge => "resource_limit"
  | .invalidFormat => "invalid_input"
  | .ioError .. => "io_error"
  | .sourceContract => "read_contract_violation"
  | .exhausted => "read_budget_exhausted"

def errorJson (e : ReadError) : Lean.Json :=
  let details := match e with
    | .ioError stage message => [("stage", Lean.toJson stage), ("message", Lean.toJson message)]
    | _ => []
  Lean.Json.mkObj ([("status", Lean.toJson (errorCode e)),
    ("authorization", Lean.toJson "blocked")] ++ details)

/-- CLI policy cap, separate from the arbitrary limits of the pure codec. -/
def cliMaxBytes : Nat := 64 * 1024 * 1024

def parseNatArg (s : String) : Option Nat := do
  if s.isEmpty || s.length > 20 then none
  else if s.toList.all (fun c => '0' ≤ c && c ≤ '9') then s.toNat? else none

def cli (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  match args with
  | [path, sizeArg, boundArg, rowArg] =>
    match parseNatArg sizeArg, parseNatArg boundArg, parseNatArg rowArg with
    | some size, some bound, some rows =>
      if size > cliMaxBytes then
        stdout.putStrLn ((Lean.Json.mkObj [("status", Lean.toJson "invalid_limits"),
          ("authorization", Lean.toJson "blocked")]).compress)
        return 2
      match ← readSnapshotFile path ⟨size, bound, rows⟩ with
      | .error e => stdout.putStrLn (errorJson e |>.compress); return 2
      | .ok result =>
        stdout.putStrLn ((Lean.Json.mkObj [
          ("status", Lean.toJson "decoded"), ("bytes_read", Lean.toJson result.bytesRead),
          ("bound", Lean.toJson result.snapshot.bound),
          ("row_length", Lean.toJson result.snapshot.row.length),
          ("mathematical_restoration", Lean.toJson "not_run"),
          ("provenance", Lean.toJson "not_verified"),
          ("authorization", Lean.toJson "blocked")]).compress)
        return 0
    | _, _, _ =>
      stdout.putStrLn ((Lean.Json.mkObj [("status", Lean.toJson "invalid_arguments"),
        ("authorization", Lean.toJson "blocked")]).compress)
      return 2
  | _ =>
    (← IO.getStderr).putStrLn
      "Usage: lake lean tools/quota_snapshot_reader.lean -- --run \
        tools/quota_snapshot_reader.lean FILE MAX_BYTES MAX_BOUND MAX_ROWS"
    return 2
end QuotaSnapshotReader

def main : List String → IO UInt32 := QuotaSnapshotReader.cli

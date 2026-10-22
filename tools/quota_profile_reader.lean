import Verification.CryptoHiddenScalarQuotaProfileCodecContract

/-! Executable IO adapter, not a formal model of the filesystem or Lean runtime.
No unbounded readBinFile, no stat-based acceptance and no mathematical restoration. -/
namespace QuotaProfileReader
open CryptoHiddenScalarQuotaProfileCodecContract
open CryptoHiddenScalarQuotaProfileContract

inductive ReadError where
  | tooLarge
  | invalidFormat
  | ioError (stage message : String)
  | sourceContract
  | exhausted
  | contextMismatch
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

structure LoadedProfile where
  bytesRead : Nat
  coefficients : List ℚ
  deriving Repr

/-- Decode exactly the accumulated bytes only after EOF; no second file read. -/
def readProfileWith (read : USize → IO ByteArray) (limits : ProfileLimits) :
    IO (Except ReadError LoadedProfile) := do
  match ← readBoundedWith read limits.maxSizeBytes with
  | .error e => return .error e
  | .ok bytes =>
    match strictDecode limits bytes with
    | none => return .error .invalidFormat
    | some coefficients => return .ok ⟨bytes.size, coefficients⟩

/-- Opens read-only. The handle does not escape the callback. Runtime handle
release is not a crash-durability guarantee or a filesystem snapshot protocol. -/
def readProfileFile (path : System.FilePath) (limits : ProfileLimits) :
    IO (Except ReadError LoadedProfile) := do
  try
    IO.FS.withFile path .read fun h => readProfileWith h.read limits
  catch e => return .error (.ioError "open" e.toString)

/-- The caller supplies n and expected independently of the file. This checks
finite coefficients, not authenticity of the caller's context. -/
def checkExpected (n : Nat) (expected : Nat → ℚ) (loaded : LoadedProfile) :
    Except ReadError LoadedProfile :=
  if Matches n expected loaded.coefficients then .ok loaded else .error .contextMismatch

def readExpectedProfileWith (read : USize → IO ByteArray) (limits : ProfileLimits)
    (n : Nat) (expected : Nat → ℚ) : IO (Except ReadError LoadedProfile) := do
  match ← readProfileWith read limits with
  | .error e => return .error e
  | .ok loaded => return checkExpected n expected loaded

def readExpectedProfileFile (path : System.FilePath) (limits : ProfileLimits)
    (n : Nat) (expected : Nat → ℚ) : IO (Except ReadError LoadedProfile) := do
  match ← readProfileFile path limits with
  | .error e => return .error e
  | .ok loaded => return checkExpected n expected loaded

def errorCode : ReadError → String
  | .tooLarge => "resource_limit"
  | .invalidFormat => "invalid_input"
  | .ioError .. => "io_error"
  | .sourceContract => "read_contract_violation"
  | .exhausted => "read_budget_exhausted"
  | .contextMismatch => "context_mismatch"

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
  | [path, sizeArg, countArg] =>
    match parseNatArg sizeArg, parseNatArg countArg with
    | some size, some count =>
      if size > cliMaxBytes then
        stdout.putStrLn ((Lean.Json.mkObj [("status", Lean.toJson "invalid_limits"),
          ("authorization", Lean.toJson "blocked")]).compress)
        return 2
      match ← readProfileFile path ⟨size, count⟩ with
      | .error e => stdout.putStrLn (errorJson e |>.compress); return 2
      | .ok result =>
        stdout.putStrLn ((Lean.Json.mkObj [
          ("status", Lean.toJson "decoded"), ("bytes_read", Lean.toJson result.bytesRead),
          ("coefficient_count", Lean.toJson result.coefficients.length),
          ("format", Lean.toJson "QCP/01"),
          ("expected_context", Lean.toJson "not_checked"),
          ("mathematical_restoration", Lean.toJson "not_run"),
          ("provenance", Lean.toJson "not_verified"),
          ("authorization", Lean.toJson "blocked")]).compress)
        return 0
    | _, _ =>
      stdout.putStrLn ((Lean.Json.mkObj [("status", Lean.toJson "invalid_arguments"),
        ("authorization", Lean.toJson "blocked")]).compress)
      return 2
  | _ =>
    (← IO.getStderr).putStrLn
      "Usage: lake env lean --run tools/quota_profile_reader.lean FILE MAX_BYTES MAX_COEFFICIENTS"
    return 2
end QuotaProfileReader

def main : List String → IO UInt32 := QuotaProfileReader.cli

import Verification.AlgebraicCertificateVerify
import Lean.Data.Json.Basic

/-! A compiled IO adapter, not a per-input kernel proof. -/
def emit (verdict : String) : IO Unit :=
  IO.println (Lean.Json.mkObj [
    ("protocol_version", Lean.Json.str "ALCC-BRIDGE-VERIFY-1"),
    ("evidence_kind", Lean.Json.str "compiled_execution"),
    ("verdict", Lean.Json.str verdict)]).compress

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--passport", passport, "--certificate", certificate] =>
    let inputs ← try
        let bp ← IO.FS.readBinFile passport
        let bc ← IO.FS.readBinFile certificate
        pure (some (bp, bc))
      catch e =>
        IO.eprintln s!"input IO failure: {e}"
        pure none
    match inputs with
    | none => emit "EXEC_IO_ERROR"; return 74
    | some (bp, bc) =>
      match AlgebraicCertificateVerify.verifyCertificateBytes bp.toList bc.toList with
      | none => emit "DECODE_ERROR"; return 3
      | some true => emit "VERIFIED_SUCCESS"; return 0
      | some false => emit "IDENTITY_MISMATCH"; return 2
  | _ =>
    IO.eprintln "usage: alcc-verify --passport FILE --certificate FILE"
    emit "EXEC_PROTOCOL_ERROR"
    return 64

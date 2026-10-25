import Verification.AlgebraicCertificateNormalizeCached
import Lean.Data.Json.Basic

/-! Experimental compiled adapter. Parsing and output serialization are not timed. -/
open AlgebraicCertificateKernel AlgebraicCertificateNormalizeCached

def readPoly (path : System.FilePath) : IO (SparsePoly 3) := do
  let text ← IO.FS.readFile path
  let mut p : SparsePoly 3 := []
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " " with
    | [x, y, z, a, b] =>
      match x.toNat?, y.toNat?, z.toNat?, a.toInt?, b.toNat? with
      | some x, some y, some z, some a, some b =>
        if b == 0 then throw (IO.userError "zero denominator")
        p := (⟨[x, y, z], rfl⟩, (a : Rat) / (b : Rat)) :: p
      | _, _, _, _, _ => throw (IO.userError "invalid integer")
    | _ => throw (IO.userError "expected five space-separated integers")
  return p.reverse

@[noinline] def runVariant (variant : String) (p : SparsePoly 3) : SparsePoly 3 :=
  if variant == "baseline" then normalize p else normalizeCached p

-- Keep computation inside a non-inlined IO call. A pure let between two clock
-- reads can be floated past the second read by the Lean compiler.
@[noinline] def compute (variant : String) (p : SparsePoly 3) : IO (SparsePoly 3 × Nat) := do
  let result := runVariant variant p
  let digest := result.foldl (fun acc t => acc + t.1.val.sum + t.2.den) 0
  return (result, digest)

def termJson (t : Term 3) : Lean.Json :=
  Lean.Json.arr #[Lean.toJson t.1.val, Lean.toJson (toString t.2.num),
    Lean.toJson (toString t.2.den)]

def runOne (args : List String) : IO UInt32 := do
  match args with
  | [variant, path] =>
    if variant != "baseline" && variant != "cached" then
      throw (IO.userError "unknown variant")
    let p ← readPoly path
    let start ← IO.monoNanosNow
    let (result, digest) ← compute variant p
    let stop ← IO.monoNanosNow
    IO.println (Lean.Json.mkObj [
      ("protocol", Lean.toJson "ALCC-NORMALIZE-PILOT-1"),
      ("variant", Lean.toJson variant),
      ("elapsed_ns", Lean.toJson (stop - start)),
      ("force_digest", Lean.toJson digest),
      ("output", Lean.Json.arr (result.map termJson).toArray)]).compress
    return 0
  | _ => throw (IO.userError "usage: alcc-normalize-bench baseline|cached INPUT")

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    -- One validation round, two warmups and eight measured rounds. Alternate
    -- order in the same process; every run emits its complete result.
    for round in List.range 11 do
      let variants := if round % 2 == 0 then ["baseline", "cached"]
        else ["cached", "baseline"]
      for variant in variants do
        let _ ← runOne [variant, path]
    return 0
  | _ => throw (IO.userError "usage: alcc-normalize-bench INPUT")

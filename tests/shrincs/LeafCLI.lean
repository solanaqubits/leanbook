import Verification.ShrincsLeaf

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let [s, d, c] := line.trimAscii.toString.splitOn " "
      | throw <| IO.userError "expected shape depth counter"
    let some shape := s.toNat? | throw <| IO.userError "bad shape"
    let some depth := d.toNat? | throw <| IO.userError "bad depth"
    let counter ← if c == "-" then pure none else do
      let some n := c.toNat? | throw <| IO.userError "bad counter"
      pure (some n)
    match ShrincsLeaf.select shape depth counter with
    | none => output.putStrLn "-"
    | some (i,h) => output.putStrLn s!"{i} {h}"

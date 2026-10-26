import Verification.CryptoBulletproofsWitnessExtraction

namespace WitnessExtractionRegression
open CryptoBulletproofsWitnessExtraction CryptoBulletproofsInnerProduct
open Examples
set_option maxRecDepth 20000

set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def replace (j : Fin 4) (f : IPAExtractionTranscript 101 (ZMod 101) 0 →
    IPAExtractionTranscript 101 (ZMod 101) 0) := Function.update honest j (f (honest j))
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongPrefix : Prefix 101 (ZMod 101) 0 := { p with P := p.P+1 }
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def rerouted := fun i => { honest i with common := wrongPrefix }
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroChallenge := replace 0 (fun t => { t with challenge := 0 })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def repeated := replace 1 (fun t => { t with challenge := 1 })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def symmetric := replace 1 (fun t => { t with challenge := -1 })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badA := replace 2 (fun t => { t with a := fun j => t.a j+1 })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badB := replace 3 (fun t => { t with b := fun j => t.b j+1 })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badL := replace 2 (fun t => { t with common := { t.common with messages := { t.common.messages
  with L := t.common.messages.L+1 } } })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badR := replace 2 (fun t => { t with common := { t.common with messages := { t.common.messages
  with R := t.common.messages.R+1 } } })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badU := replace 0 (fun t => { t with common := { t.common with U := 12 } })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badG := replace 0 (fun t => { t with common := { t.common with G := ![3,3] } })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badH := replace 0 (fun t => { t with common := { t.common with H := ![5,8] } })
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def isWitness (r : Except ExtractionError (ExtractionResult 101 0)) : Bool :=
  match r with | .ok (.witness _ _) => true | _ => false
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def isRelation (r : Except ExtractionError (ExtractionResult 101 0)) : Bool :=
  match r with | .ok (.relation _) => true | _ => false

set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def honestK (k : ℕ) : Prefix 101 (ZMod 101) k × (Fin 4 → IPAExtractionTranscript 101 (ZMod 101) k)
  :=
  let G : Vec (k+1) (ZMod 101) := fun j => j.val+2
  let H : Vec (k+1) (ZMod 101) := fun j => j.val+5
  let aa : Vec (k+1) (ZMod 101) := join (fun _ => 2) (fun _ => 5)
  let bb : Vec (k+1) (ZMod 101) := join (fun _ => 7) (fun _ => 9)
  let pp : Prefix 101 (ZMod 101) k := ⟨11,G,H,ipa_target 11 G H aa bb, round_messages 11 G H aa bb⟩
  (pp, fun i => ⟨pp, units i, fold_vector_a (units i) aa, fold_vector_b (units i) bb⟩)

set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def xs : Fin 3 → ZMod 101 := ![1,2,3]
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ys : Fin 3 → ZMod 101 := fun i => 7+9*xs i+11*(xs i)^2

set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : CryptoBulletproofsWitnessExtractionSuite := verification_suite
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p honest = .ok (.witness a b) := non_vacuous_extraction_success
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ c, extract_ipa_witness p inconsistent = .ok (.relation c) ∧ c ≠ 0 ∧
    evaluate p.U p.G p.H c = 0 := non_vacuous_relation
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : p.P = 59 := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : p.messages.L = 47 := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : p.messages.R = 40 := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Function.Injective (fun i => (units i : ZMod 101)^2) := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ i, Accepts p (units i) (honest i).a (honest i).b := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ i, Accepts p (units i) (inconsistent i).a (inconsistent i).b := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p zeroChallenge = .error .zeroChallenge := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p repeated = .error .repeatedSquare := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p symmetric = .error .repeatedSquare := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p rerouted = .error .prefixMismatch := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness wrongPrefix rerouted = .error .invalidResponse := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p badA = .error .invalidResponse := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p badB = .error .invalidResponse := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p badL = .error .prefixMismatch := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p badR = .error .prefixMismatch := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p badU = .error .prefixMismatch := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p badG = .error .prefixMismatch := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract_ipa_witness p badH = .error .prefixMismatch := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : interpolate_quad xs ys = ![7,9,11] := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (vandermonde_matrix xs).det = 2 := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (vandermonde_matrix (![1,1,3] : Fin 3 → ZMod 101)).det = 0 := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : interpolate_quad xs (fun _ => 0) = 0 := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : interpolate_quad xs (fun _ => 1) = ![1,0,0] := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : interpolate_quad xs xs = ![0,1,0] := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : interpolate_quad xs (fun i => (xs i)^2) = ![0,0,1] := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extract_ipa_witness (honestK 1).1 (honestK 1).2).isOk = true := by decide +kernel
set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extract_ipa_witness (honestK 2).1 (honestK 2).2).isOk = true := by decide +kernel

end WitnessExtractionRegression
open WitnessExtractionRegression CryptoBulletproofsWitnessExtraction
  CryptoBulletproofsWitnessExtraction.Examples

set_option maxHeartbeats 1200000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [
    isWitness (extract_ipa_witness p honest),
    isRelation (extract_ipa_witness p inconsistent),
    decide (extract_ipa_witness p zeroChallenge = .error .zeroChallenge),
    decide (extract_ipa_witness p repeated = .error .repeatedSquare),
    decide (extract_ipa_witness p symmetric = .error .repeatedSquare),
    decide (extract_ipa_witness p rerouted = .error .prefixMismatch),
    decide (extract_ipa_witness wrongPrefix rerouted = .error .invalidResponse),
    decide (extract_ipa_witness p badA = .error .invalidResponse),
    decide (extract_ipa_witness p badB = .error .invalidResponse),
    decide (extract_ipa_witness p badL = .error .prefixMismatch),
    decide (extract_ipa_witness p badR = .error .prefixMismatch),
    decide (extract_ipa_witness p badU = .error .prefixMismatch),
    decide (extract_ipa_witness p badG = .error .prefixMismatch),
    decide (extract_ipa_witness p badH = .error .prefixMismatch),
    decide (interpolate_quad xs ys = ![7,9,11]),
    decide ((vandermonde_matrix xs).det = 2),
    decide ((vandermonde_matrix (![1,1,3] : Fin 3 → ZMod 101)).det = 0),
    decide (interpolate_quad xs (fun _ => 0) = 0),
    decide (interpolate_quad xs (fun _ => 1) = ![1,0,0]),
    decide (interpolate_quad xs xs = ![0,1,0]),
    decide (interpolate_quad xs (fun i => (xs i)^2) = ![0,0,1]),
    (extract_ipa_witness (honestK 1).1 (honestK 1).2).isOk,
    (extract_ipa_witness (honestK 2).1 (honestK 2).2).isOk,
    isWitness (extract_ipa_witness p (fun i => honest (3-i))),
    decide (∀ i, Accepts p (units i) (inconsistent i).a (inconsistent i).b),
    decide (p.P = 59), decide (p.messages.L = 47), decide (p.messages.R = 40)]
  for (check, i) in checks.zipIdx do
    unless check do throw (IO.userError s!"WITNESS_EXTRACTION_FAILED {i}")
  IO.println s!"WITNESS_EXTRACTION_OK {checks.length}"

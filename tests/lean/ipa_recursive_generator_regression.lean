/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPARecursiveTreeGeneratorContract

namespace IPARecursiveRegression
open CryptoBulletproofsIPARecursiveTreeGeneratorContract
open CryptoBulletproofsTreeExtraction CryptoBulletproofsInnerProduct
open CryptoBulletproofsIPATreeProbabilityContract
set_option maxRecDepth 50000

-- Nonzero generators; zero witness. No completed child trees enter the source.
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def s (k : ℕ) : Statement 101 (ZMod 101) k := ⟨1, fun _ => 1, fun _ => 2, 0⟩
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def msg : RoundMessages (ZMod 101) := ⟨0, 0⟩
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls : Fin 4 → ZMod 101 := ![1, 2, 3, 4]
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def src : Source 101 (ZMod 101) Bool where
  leaf s w := if w then some (s, 0, 0) else none
  node _ s _ := some (s, msg, calls)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def full : (k : ℕ) → Tape Bool k
  | 0 => true
  | k + 1 => (true, fun _ => full k)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def oneBad : Tape Bool 1 := (true, fun i => if i = 2 then false else true)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def deepBad : Tape Bool 2 := (true, fun i => if i = 1 then oneBad else full 1)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def C : Finset Bool := Finset.univ

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def missing : Source 101 (ZMod 101) Bool := { src with leaf := fun _ _ => none }
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongScalar : Source 101 (ZMod 101) Bool := { src with leaf := fun s _ => some (s, 1, 0) }
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongContext : Source 101 (ZMod 101) Bool :=
  { src with leaf := fun s _ => some ({ s with P := s.P + 1 }, 0, 0) }
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongHeader : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some ({ s with P := s.P + 1 }, msg, calls) }
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroCall : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some (s, msg, ![0, 2, 3, 4]) }
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def oppositeCall : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some (s, msg, ![1, -1, 3, 4]) }

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate src (s 0) (full 0)).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate src (s 1) (full 1)).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate src (s 2) (full 2)).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate src (s 1) oneBad).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate src (s 2) deepBad).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate missing (s 1) (full 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate wrongScalar (s 1) (full 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate wrongContext (s 1) (full 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate wrongHeader (s 1) (full 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate zeroCall (s 1) (full 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate oppositeCall (s 1) (full 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extract src (s 1) (full 1)).isOk = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extract src (s 2) (full 2)).isOk = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract src (s 2) deepBad = .error "recursiveCandidateUnavailable" := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (tapes C 0).card = 2 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (tapes C 1).card = 32 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (tapes C 2).card = 2097152 := by rw [tapes_card]; decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (good C src (s 0)).card = 1 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (good C src (s 1)).card = 2 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate C src (s 0) = 1/2 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate C src (s 1) = 1/16 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate C missing (s 1) = 0 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate C wrongContext (s 1) = 0 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate C wrongScalar (s 1) = 0 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate C zeroCall (s 1) = 0 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate ({true} : Finset Bool) src (s 2) = 1 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerBound 1 (1 / 2) 2 = 1/65536 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkCount 2 = 21 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (t : IPATranscriptTree 101 (ZMod 101) 2) : leafCount t = 16 := leafCount_eq t

-- Correlated reuse across the four child coordinates: each marginal is 1/2,
-- joint success is 1/2 rather than the independent 1/16.
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def diagonal (w : Bool) : Tape Bool 1 := (w, fun _ => w)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability C (C.filter (fun w => (generate src (s 1) (diagonal w)).isSome)) = 1/2 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability C (C.filter (fun w => (generate src (s 1) (diagonal w)).isSome)) ≠
    rate C src (s 1) := by decide +kernel

-- A parent challenge changes P; a scalar response for the old P must fail.
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def moving : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some (s, ⟨1, 0⟩, calls) }
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (header moving (s 1) true).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate moving (s 1) (full 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate C moving (s 1) = 0 := by decide +kernel

-- A nonzero opening is also checked (P=G*3).
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def nonzeroLeaf : Source 101 (ZMod 101) Bool :=
  { src with leaf := fun s _ => some (s, 3, 0) }
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate nonzeroLeaf { s 0 with P := 3 } true).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate nonzeroLeaf { s 0 with P := 4 } true).isSome = false := by decide +kernel

-- The reusable conditional theorem applies to actual generated output.
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (h : Dense C src 1 (1 / 2) (s 2)) : 1/65536 ≤ rate C src (s 2) := by
  have he : lowerBound 1 (1 / 2) 2 = 1/65536 := by decide +kernel
  rw [← he]
  exact recursive_probability_lower C (by decide +kernel) src 1 (1 / 2)
    (by norm_num) (by norm_num) (s 2) h
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (h : Dense C src 1 (1 / 2) (s 2)) :
    ∃ w ∈ tapes C 2, ∃ r, extract src (s 2) w = .ok r ∧ ResultValid (s 2) r :=
  dense_extracts C (by decide +kernel) src 1 (1 / 2) (by norm_num) (by norm_num) (s 2) h
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : CryptoBulletproofsIPABoundedRetryContract.RetryBounds
    (CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.productTapes (tapes C 1) 3)
    (CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.tapeAttempt
      (fun w => (generate src (s 1) w).isSome)) (fun _ => rate C src (s 1)) 3 :=
  recursive_retry_bounds C (by decide +kernel) src (s 1) 3

-- Availability is witnessed by the actual finite table, not assumed for this example.
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem dense_one : Dense C src 1 (1 / 2) (s 1) := by
  refine ⟨C, Finset.Subset.refl C, ?_, ?_⟩
  · decide +kernel
  · intro w hw
    refine ⟨msg, CryptoBulletproofsWitnessExtraction.Examples.units, ?_, ?_⟩
    · cases w <;> decide +kernel
    · intro i
      fin_cases i <;> unfold CryptoBulletproofsIPARecursiveTreeGeneratorContract.Dense <;> decide
        +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1/16 ≤ rate C src (s 1) := by
  have h := recursive_probability_lower C (by decide +kernel) src 1 (1 / 2)
    (by norm_num) (by norm_num) (s 1) dense_one
  norm_num [lowerBound] at h ⊢
  exact h
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ w ∈ tapes C 1, ∃ r, extract src (s 1) w = .ok r ∧ ResultValid (s 1) r :=
  dense_extracts C (by decide +kernel) src 1 (1 / 2) (by norm_num) (by norm_num) (s 1) dense_one
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((generate src (s 2) (full 2)).map leafCount) = some 16 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((generate src (s 1) (full 1)).map leafCount) = some 4 := by decide +kernel

end IPARecursiveRegression
open IPARecursiveRegression CryptoBulletproofsIPARecursiveTreeGeneratorContract

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [
    (generate src (s 0) (full 0)).isSome,
    (generate src (s 1) (full 1)).isSome,
    (generate src (s 2) (full 2)).isSome,
    !(generate src (s 1) oneBad).isSome,
    !(generate src (s 2) deepBad).isSome,
    !(generate missing (s 1) (full 1)).isSome,
    !(generate wrongScalar (s 1) (full 1)).isSome,
    !(generate wrongContext (s 1) (full 1)).isSome,
    !(generate wrongHeader (s 1) (full 1)).isSome,
    !(generate zeroCall (s 1) (full 1)).isSome,
    !(generate oppositeCall (s 1) (full 1)).isSome,
    (extract src (s 1) (full 1)).isOk,
    (extract src (s 2) (full 2)).isOk,
    decide (rate C src (s 1) = 1/16),
    decide (rate C missing (s 1) = 0),
    !(generate moving (s 1) (full 1)).isSome]
  unless checks.all id do throw (IO.userError "recursive IPA regression failed")
  IO.println s!"IPA_RECURSIVE_OK {checks.length}"

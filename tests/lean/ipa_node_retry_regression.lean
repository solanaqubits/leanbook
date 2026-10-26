/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract

namespace IPANodeRetryRegression
open CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract
open CryptoBulletproofsTreeExtraction CryptoBulletproofsInnerProduct
open CryptoBulletproofsIPARecursiveTreeGeneratorContract (Source leafCount leafCount_eq)
open CryptoBulletproofsIPATreeProbabilityContract (probability)
set_option maxRecDepth 50000

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def s (k : ℕ) : Statement 101 (ZMod 101) k := ⟨1, fun _ => 1, fun _ => 2, 0⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def msg : RoundMessages (ZMod 101) := ⟨0, 0⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls : Fin 4 → ZMod 101 := ![1, 2, 3, 4]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def src : Source 101 (ZMod 101) Bool where
  leaf s w := if w then some (s, 0, 0) else none
  node _ s _ := some (s, msg, calls)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def two (_ : ℕ) : ℕ := 2
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def one (_ : ℕ) : ℕ := 1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zero (_ : ℕ) : ℕ := 0
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def full (budget : ℕ → ℕ) : (k : ℕ) → Tape budget Bool k
  | 0 => true
  | k + 1 => fun _ => (true, fun _ => full budget k)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def failedThenGood : Tape two Bool 1 := fun j => (true, fun _ => decide (j.val = 1))
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def allBad : Tape two Bool 1 := fun _ => (true, fun _ => false)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def goodThenBad : Tape two Bool 1 := fun j => (true, fun _ => decide (j.val = 0))
-- Only the children have two attempts. The parent has one and cannot retry a whole tree.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def childOnly (k : ℕ) : ℕ := if k = 1 then 2 else 1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def recoveredChildren : Tape childOnly Bool 2 :=
  fun _ => (true, fun _ => fun j => (true, fun _ => decide (j.val = 1)))
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def firstChildrenOnly : CryptoBulletproofsIPARecursiveTreeGeneratorContract.Tape Bool 2 :=
  (true, fun _ => (true, fun _ => false))
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def C : Finset Bool := Finset.univ

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def missing : Source 101 (ZMod 101) Bool := { src with leaf := fun _ _ => none }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongScalar : Source 101 (ZMod 101) Bool := { src with leaf := fun s _ => some (s, 1, 0) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongContext : Source 101 (ZMod 101) Bool :=
  { src with leaf := fun s _ => some ({ s with P := s.P + 1 }, 0, 0) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongHeader : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some ({ s with P := s.P + 1 }, msg, calls) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroCall : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some (s, msg, ![0, 2, 3, 4]) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def oppositeCall : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some (s, msg, ![1, -1, 3, 4]) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def moving : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ s _ => some (s, ⟨1, 0⟩, calls) }

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : retry (![none, some 7] : Fin 2 → Option ℕ) = some 7 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : retry (![some 7, some 8] : Fin 2 → Option ℕ) = some 7 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : retry (![none, none] : Fin 2 → Option ℕ) = none := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two src (s 0) true).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two src (s 0) false).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two src (s 1) failedThenGood).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two src (s 1) goodThenBad).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two src (s 1) allBad).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate zero src (s 1) (full zero 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate childOnly src (s 2) recoveredChildren).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (CryptoBulletproofsIPARecursiveTreeGeneratorContract.generate
    src (s 2) firstChildrenOnly).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((generate childOnly src (s 2) recoveredChildren).map leafCount) = some 16 :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((generate two src (s 1) failedThenGood).map leafCount) = some 4 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two missing (s 2) (full two 2)).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two wrongScalar (s 1) (full two 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two wrongContext (s 1) (full two 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two wrongHeader (s 1) (full two 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two zeroCall (s 1) (full two 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two oppositeCall (s 1) (full two 1)).isSome = false := by decide +kernel
-- The source returns the newly requested identity, but a scalar for the old P.
-- Leaf equation checking rejects it, independently of the claimed identity.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (generate two moving (s 1) (full two 1)).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extract two src (s 1) failedThenGood).isOk = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extract childOnly src (s 2) recoveredChildren).isOk = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extract two src (s 1) allBad = .error "nodeRetryBudgetExhausted" := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (tapes two C 0).card = 2 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (tapes two C 1).card = 1024 := by rw [tapes_card]; decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (tapes childOnly C 2).card = 2199023255552 := by
  rw [tapes_card, tapes_card]; decide +kernel

-- A finite reference count of full attempts; computation is deliberately small.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def localGood : Finset (Tape two Bool 1) :=
  (tapes two C 1).filter (fun w => (generate two src (s 1) w).isSome)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : localGood.card = 124 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability (tapes two C 1) localGood = 31/256 := by decide +kernel

-- Repeating one whole attempt keeps its original success probability 1/16.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def attemptSpace : Finset (Bool × (Fin 4 → Bool)) :=
  C ×ˢ Fintype.piFinset (fun _ : Fin 4 => C)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def duplicate (w : Bool × (Fin 4 → Bool)) : Tape two Bool 1 := fun _ => w
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability attemptSpace (attemptSpace.filter
    (fun w => (generate two src (s 1) (duplicate w)).isSome)) = 1/16 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1/16 : ℚ) < 31/256 := by norm_num

-- Opposite child marginals each accept half their inputs, but never jointly.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def antiShared (w : Bool) : Tape two Bool 1 :=
  fun _ => (true, fun i => if i.val % 2 = 0 then w else !w)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability C (C.filter
    (fun w => (generate two src (s 1) (antiShared w)).isSome)) = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (0 : ℚ) < 1 - (1 - (1/2 : ℚ)^4)^2 := by norm_num

-- Reuse across attempts and across children has a different probability law.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def shared (w : Bool) : Tape two Bool 1 := fun _ => (w, fun _ => w)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability C (C.filter (fun w => (generate two src (s 1) (shared w)).isSome)) = 1/2 :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1 - (1 - (1/2 : ℚ))^2) = 3/4 := by norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1/2 : ℚ) ≠ 1 - (1 - (1/2 : ℚ))^2 := by norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1/2 : ℚ) ≠ (1/2 : ℚ)^4 := by norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1 - (1 - (1/2 : ℚ)^4)^2) = 31/256 := by norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1 - (1 - (31/256 : ℚ)^4)^2) =
    7932132093300991/18446744073709551616 := by norm_num

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (w : Tape two Bool 2) (t : IPATranscriptTree 101 (ZMod 101) 2)
    (h : generate two src (s 2) w = some t) : ValidAcceptingTree (s 2) t :=
  generate_valid two src (s 2) w t h
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (w : Tape two Bool 2) (t : IPATranscriptTree 101 (ZMod 101) 2)
    (h : generate two src (s 2) w = some t) :
    ∃ r, extract two src (s 2) w = .ok r ∧ ResultValid (s 2) r :=
  generated_extracts two src (s 2) w t h
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (r : TreeExtractionResult 101 2)
    (h : extract childOnly src (s 2) recoveredChildren = .ok r) : ResultValid (s 2) r :=
  extract_sound childOnly src (s 2) recoveredChildren r h

-- The declared availability is checked against the actual finite source table.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem dense_one : CryptoBulletproofsIPARecursiveTreeGeneratorContract.Dense
    C src 1 (1/2) (s 1) := by
  refine ⟨C, Finset.Subset.refl C, ?_, ?_⟩
  · decide +kernel
  · intro w hw
    refine ⟨msg, CryptoBulletproofsWitnessExtraction.Examples.units, ?_, ?_⟩
    · cases w <;> decide +kernel
    · intro i
      fin_cases i <;> unfold CryptoBulletproofsIPARecursiveTreeGeneratorContract.Dense <;>
        decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerBound two 1 (1/2) 1 = 31/256 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerBound two 1 (1/2) 2 =
    7932132093300991/18446744073709551616 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerBound childOnly 1 (1/2) 2 = 923521/4294967296 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 31/256 ≤ rate two C src (s 1) := by
  have h := recursive_probability_lower two C (by decide +kernel) src 1 (1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (s 1) dense_one
  norm_num [lowerBound, amplify, two] at h ⊢
  exact h
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : CryptoBulletproofsIPABoundedRetryContract.RetryBounds (tapes two C 1)
    (CryptoBulletproofsIPAProductTapeCandidateGeneratorContract.tapeAttempt
      (fun w => (attempt two src (s 1) w).isSome))
    (fun _ => attemptRate two C src (s 1)) 2 :=
  node_retry_bounds two C (by decide +kernel) src (s 1)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerBound one 1 (1/2) 2 ≤ lowerBound two 1 (1/2) 2 :=
  lowerBound_mono_budget one two 1 (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by intro j; simp [one, two]) 2
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : amplify (1/16) 1 < amplify (1/16) 2 :=
  amplify_strict_budget (1/16) (by norm_num) (by norm_num) (by decide +kernel)
-- A strict lower estimate below 1 does not force actual strict growth at saturation.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : amplify 1 1 = amplify 1 2 := by norm_num [amplify]

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate two C src (s 1) = 31/256 := by
  rw [rate_node_exact two C (by decide +kernel)]
  have h : attemptRate two C src (s 1) = 1/16 := by decide +kernel
  rw [h]
  norm_num [amplify, two]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate one C src (s 2) ≤ rate two C src (s 2) :=
  rate_mono_budget one two C (by decide +kernel) src
    (by intro j; simp [one, two]) (s 2)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : CryptoBulletproofsIPARecursiveTreeGeneratorContract.rate C src (s 2) ≤
    rate two C src (s 2) :=
  rate_ge_single two C (by decide +kernel) src (by intro j; simp [two]) (s 2)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rate one C src (s 2) =
    CryptoBulletproofsIPARecursiveTreeGeneratorContract.rate C src (s 2) :=
  rate_single_budget C (by decide +kernel) src (s 2)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ w ∈ tapes two C 1, ∃ r, extract two src (s 1) w = .ok r ∧ ResultValid (s 1) r :=
  dense_extracts two C (by decide +kernel) src 1 (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by intro j; simp [two]) (s 1) dense_one

end IPANodeRetryRegression
open IPANodeRetryRegression CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [
    (generate two src (s 0) true).isSome,
    !(generate two src (s 0) false).isSome,
    (generate two src (s 1) failedThenGood).isSome,
    (generate two src (s 1) goodThenBad).isSome,
    !(generate two src (s 1) allBad).isSome,
    !(generate zero src (s 1) (full zero 1)).isSome,
    (generate childOnly src (s 2) recoveredChildren).isSome,
    !(generate two missing (s 2) (full two 2)).isSome,
    !(generate two wrongScalar (s 1) (full two 1)).isSome,
    !(generate two wrongContext (s 1) (full two 1)).isSome,
    !(generate two wrongHeader (s 1) (full two 1)).isSome,
    !(generate two zeroCall (s 1) (full two 1)).isSome,
    !(generate two oppositeCall (s 1) (full two 1)).isSome,
    !(generate two moving (s 1) (full two 1)).isSome,
    (extract two src (s 1) failedThenGood).isOk,
    (extract childOnly src (s 2) recoveredChildren).isOk,
    decide (localGood.card = 124),
    decide (retry (![some 7, some 8] : Fin 2 → Option ℕ) = some 7)]
  unless checks.all id do throw (IO.userError "node-local IPA retry regression failed")
  IO.println s!"IPA_NODE_RETRY_OK {checks.length}"

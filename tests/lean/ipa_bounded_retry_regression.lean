/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPABoundedRetryContract

namespace IPABoundedRetryRegression
open CryptoBulletproofsIPABoundedRetryContract
open CryptoBulletproofsIPATreeProbabilityContract
open CryptoBulletproofsTreeExtraction CryptoBulletproofsInnerProduct
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

def tapes : Finset (Fin 4) := Finset.univ
def independentBits (i : ℕ) (w : Fin 4) : Bool :=
  if i = 0 then w.val % 2 == 0 else w.val < 2
def repeated (_ : ℕ) (w : Bool) : Bool := w
def bits : Finset Bool := {false,true}

example : firstSuccess (fun _ => true) 0 = none := rfl
example : firstSuccess (fun _ => true) 1 = some 0 := by decide +kernel
example : firstSuccess (fun _ => true) 5 = some 0 := by decide +kernel
example : firstSuccess (fun _ => false) 5 = none := by decide +kernel
example : firstSuccess (fun i => i == 2) 2 = none := by decide +kernel
example : firstSuccess (fun i => i == 2) 3 = some 2 := by decide +kernel
example : attempts (fun _ => true) 0 = 0 := rfl
example : attempts (fun _ => true) 5 = 1 := by decide +kernel
example : attempts (fun _ => false) 5 = 5 := by decide +kernel
example : attempts (fun i => i == 2) 8 = 3 := by decide +kernel
example : firstSuccess (fun i => i == 2) 100 = some 2 :=
  firstSuccess_extend _ 3 100 2 (by omega) (by decide +kernel)
example : RetryBounds tapes independentBits (fun _ => 1/2) 2 := by decide +kernel
example : probability tapes (successes tapes independentBits 2) = 3/4 := by decide +kernel
example : probability tapes (failures tapes independentBits 2) = 1/4 := by decide +kernel
example : expectedAttempts tapes independentBits 0 = 0 := by decide +kernel
example : expectedAttempts tapes independentBits 1 = 1 := by decide +kernel
example : expectedAttempts tapes independentBits 2 = 3/2 := by decide +kernel
example : (3/4 : ℚ) ≤ probability tapes (successes tapes independentBits 2) := by
  convert constant_success_bound tapes (by decide +kernel) independentBits (1/2) 2
    (by decide +kernel) using 1; norm_num
example : expectedAttempts tapes independentBits 2 ≤ 2 := by
  simpa using expected_attempts_le_inverse tapes (by decide +kernel) independentBits (1/2)
    (by norm_num) (by norm_num) 2 (by decide +kernel)
example : RetryBounds bits repeated (fun _ => 0) 5 := by decide +kernel
example : RetryBounds bits (fun _ _ => true) (fun _ => 1) 5 := by decide +kernel
example : probability bits (successes bits (fun _ _ => true) 5) = 1 := by decide +kernel
example : ¬ RetryBounds bits (fun _ _ => false) (fun _ => 1) 1 := by decide +kernel
example : RetryBounds (∅ : Finset Bool) repeated (fun _ => 1) 3 := by decide +kernel
example : expectedAttempts (∅ : Finset Bool) repeated 3 = 0 := by decide +kernel
/-- Identical retries have successful marginals but no amplification. -/
example : probability bits (bits.filter (fun w => repeated 0 w)) = 1/2 := by decide +kernel
example : probability bits (bits.filter (fun w => repeated 1 w)) = 1/2 := by decide +kernel
example : probability bits (successes bits repeated 4) = 1/2 := by decide +kernel
example : ¬ RetryBounds bits repeated (fun _ => 1/2) 2 := by decide +kernel
example : (1-(1-(1/2 : ℚ))^4) > probability bits (successes bits repeated 4) := by decide +kernel
example : expectedAttempts bits repeated 4 = 5/2 := by decide +kernel

-- Nonzero-generator honest tree from the existing extractor's checked fixture.
def s := Examples.s 1
def good := Examples.honest 1
def bad : IPATranscriptTree 101 (ZMod 101) 1 :=
  .node { s with P := s.P + 1 } ⟨0,0⟩ ![1,2,3,4]
    (fun _ => .leaf (Examples.s 0) 0 0)
def candidates (i : ℕ) (w : Fin 4) := if independentBits i w then good else bad
def localFactors (_ : ℕ) : List ℚ := [1/2,1,1,1,1]
example : ValidAcceptingTree s good := by decide +kernel
example : ¬ ValidAcceptingTree s bad := by decide +kernel
example : ∀ i < 2, ∀ w, checkedAttempt s candidates i w = independentBits i w := by decide +kernel
example : ∀ i < 2, ConditionalBounds (failures tapes (checkedAttempt s candidates) i)
    (treeTests s (candidates i)) (localFactors i) := by decide +kernel

theorem candidate_bounds : RetryBounds tapes (checkedAttempt s candidates) (fun _ => 1/2) 2 :=
  conditional_tree_retry_bounds tapes s candidates (fun _ => 1/2) localFactors 2
    (by decide +kernel) (by decide +kernel)
example : (3/4 : ℚ) ≤ probability tapes
    (tapes.filter (fun w => (boundedExtract s candidates 2 w).isOk = true)) := by
  convert bounded_extraction_probability tapes (by decide +kernel) s candidates
    (fun _ => 1/2) localFactors 2 (by decide +kernel) (by decide +kernel) using 1; norm_num
example : expectedAttempts tapes (checkedAttempt s candidates) 2 ≤ 2 := by
  simpa using expected_attempts_le_inverse tapes (by decide +kernel) (checkedAttempt s candidates)
    (1/2) (by norm_num) (by norm_num) 2 candidate_bounds
example : (boundedExtract s candidates 0 0).isOk = false := by decide +kernel
example : (boundedExtract s candidates 1 1).isOk = false := by decide +kernel
example : (boundedExtract s candidates 2 1).isOk = true := by decide +kernel
example : (boundedExtract s candidates 2 3).isOk = false := by decide +kernel
example : boundedExtract s candidates 8 1 = boundedExtract s candidates 2 1 :=
  boundedExtract_extend s candidates 2 8 1 (by omega) (by decide +kernel)
example : ∃ w ∈ tapes, ∃ r, boundedExtract s candidates 2 w = .ok r ∧ ResultValid s r :=
  positive_bounded_extraction tapes s candidates 2 (by decide +kernel)

-- Valid root data do not excuse a child with a substituted statement.
def zs (k : ℕ) : Statement 101 (ZMod 101) k := ⟨0,0,0,0⟩
def wrongChild : IPATranscriptTree 101 (ZMod 101) 1 :=
  .node (zs 1) ⟨0,0⟩ ![1,2,3,4] (fun _ => .leaf { zs 0 with P := 1 } 0 0)
example : ¬ ValidAcceptingTree (zs 1) wrongChild := by decide +kernel
example : (boundedExtract (zs 1) (fun _ (_ : Bool) => wrongChild) 3 true).isOk = false :=
  by decide +kernel
example : (boundedExtract { s with P := s.P + 1 } candidates 3 0).isOk = false :=
  by decide +kernel

def checks : List Bool := [
  firstSuccess (fun _ => true) 0 == none,
  firstSuccess (fun _ => true) 5 == some 0,
  firstSuccess (fun _ => false) 5 == none,
  firstSuccess (fun i => i == 2) 3 == some 2,
  attempts (fun _ => true) 5 == 1,
  attempts (fun _ => false) 5 == 5,
  attempts (fun i => i == 2) 8 == 3,
  decide (probability tapes (successes tapes independentBits 2) = 3/4),
  decide (expectedAttempts tapes independentBits 2 = 3/2),
  decide (probability bits (successes bits repeated 4) = 1/2),
  decide (¬ RetryBounds bits repeated (fun _ => 1/2) 2),
  !(boundedExtract s candidates 1 1).isOk,
  (boundedExtract s candidates 2 1).isOk,
  !(boundedExtract s candidates 2 3).isOk,
  !(boundedExtract (zs 1) (fun _ (_ : Bool) => wrongChild) 3 true).isOk,
  decide (ValidAcceptingTree s good)]
end IPABoundedRetryRegression

def main : IO Unit := do
  if IPABoundedRetryRegression.checks.all id then IO.println "IPA_BOUNDED_RETRY_OK 16"
  else throw (IO.userError "bounded retry regression failure")

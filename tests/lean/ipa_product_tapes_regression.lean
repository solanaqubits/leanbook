/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAProductTapeCandidateGeneratorContract

namespace IPAProductTapeRegression
open CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoBulletproofsIPAFiniteForkingProbabilityContract
open CryptoBulletproofsIPATreeProbabilityContract
set_option maxRecDepth 50000

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def s := Examples.s 1
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def msg : RoundMessages (ZMod 101) :=
  match Examples.honest 1 with | .node _ m _ _ => m
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def children : Fin 4 → IPATranscriptTree 101 (ZMod 101) 0 :=
  match Examples.honest 1 with | .node _ _ _ ts => ts
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def raw (x : ZMod 101) : Option (IPATranscriptTree 101 (ZMod 101) 0) :=
  if x = 1 then some (children 0) else
  if x = 2 then some (children 1) else
  if x = 3 then some (children 2) else
  if x = 4 then some (children 3) else none
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls : List (ZMod 101) := [1,2,3,4]

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedReplies s msg raw 1).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedReplies s msg raw 0 = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedReplies s msg raw 5 = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (candidate s msg calls raw calls).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (candidate s msg calls raw [4,3,2,1]).isSome = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate s msg calls raw [1,1,3,4] = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate s msg calls raw [1,2,3] = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate s msg calls raw [1,2,3,5] = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extractCandidate s msg calls raw calls).isOk = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extractCandidate s msg calls raw [1,1,3,4] = .error "candidateUnavailable" :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (replySet calls (checkedReplies s msg raw)).card = 4 := by decide +kernel

-- Missing replies must remain missing even when a synthetic zero child is valid.
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zs (k : ℕ) : Statement 101 (ZMod 101) k := ⟨0,0,0,0⟩
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zm : RoundMessages (ZMod 101) := ⟨0,0⟩
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def absent (_ : ZMod 101) : Option (IPATranscriptTree 101 (ZMod 101) 0) := none
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroReply (_ : ZMod 101) : Option (IPATranscriptTree 101 (ZMod 101) 0) :=
  some (.leaf (zs 0) 0 0)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongReply (_ : ZMod 101) : Option (IPATranscriptTree 101 (ZMod 101) 0) :=
  some (.leaf { zs 0 with P := 1 } 0 0)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ValidAcceptingTree (zs 1) (drawTree (zs 1) zm absent calls) := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate (zs 1) zm calls absent calls = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedReplies (zs 1) zm wrongReply 1 = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate (zs 1) zm calls wrongReply calls = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedReplies (zs 1) zm zeroReply 0 = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate (zs 1) zm [0,1,2,3] zeroReply [0,1,2,3] = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate (zs 1) zm [1,-1,2,3] zeroReply [1,-1,2,3] = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : candidate (zs 1) zm [1,2,3] zeroReply calls = none := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (replySet [1,2,3,4,5,6,7] (checkedReplies (zs 1) zm zeroReply)).card = 7 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < probability (samples ([1,2,3,4,5,6,7] : List (ZMod 101)).toFinset 4)
    ((samples ([1,2,3,4,5,6,7] : List (ZMod 101)).toFinset 4).filter
      (fun l => (candidate (zs 1) zm [1,2,3,4,5,6,7] zeroReply l).isSome = true)) :=
  candidate_probability_positive _ _ _ _ (by decide +kernel)


open CryptoBulletproofsIPABoundedRetryContract

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def small : Finset (List (ZMod 101)) := {calls, [1,1,3,4]}
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def accepts := candidateAccepted s msg calls raw
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : singleProbability small accepts = 1/2 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (productTapes small 0).card = 1 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (productTapes small 1).card = 2 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (productTapes small 2).card = 4 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (productTapes small 3).card = 8 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (CryptoBulletproofsIPABoundedRetryContract.successes
    (productTapes small 1) (tapeAttempt accepts) 1).card = 1 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (CryptoBulletproofsIPABoundedRetryContract.successes
    (productTapes small 2) (tapeAttempt accepts) 2).card = 3 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (CryptoBulletproofsIPABoundedRetryContract.successes
    (productTapes small 3) (tapeAttempt accepts) 3).card = 7 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (failures (productTapes small 3) (tapeAttempt accepts) 3).card = 1 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : RetryBounds (productTapes small 3) (tapeAttempt accepts) (fun _ => 1/2) 3 := by
  simpa only [show singleProbability small accepts = 1/2 by decide +kernel] using
    product_retry_bounds small (by decide +kernel) accepts 3
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : expectedAttempts (productTapes small 3) (tapeAttempt accepts) 3 = 7/4 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : expectedAttempts (productTapes small 3) (tapeAttempt accepts) 3 ≤ 2 := by
  convert product_expected_le_inverse small (by decide +kernel) accepts
    (by decide +kernel) 3 using 1
  decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability small (CryptoBulletproofsIPABoundedRetryContract.successes
    small (fun _ w => accepts w) 3) = 1/2 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability (productTapes small 2) (CryptoBulletproofsIPABoundedRetryContract.successes
    (productTapes small 2) (tapeAttempt accepts) 2) = 3/4 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability small (CryptoBulletproofsIPABoundedRetryContract.successes
    small (fun _ w => accepts w) 2) < 1-(1-singleProbability small accepts)^2 :=
  diagonal_not_amplified small accepts 2 (by omega) (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ RetryBounds small (fun _ w => accepts w) (fun _ => 1/2) 2 := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : RetryBounds (productTapes small 3) (tapeAttempt (fun _ => false)) (fun _ => 0) 3 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : RetryBounds (productTapes small 3) (tapeAttempt (fun _ => true)) (fun _ => 1) 3 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : RetryBounds (productTapes small 0) (tapeAttempt accepts) (fun _ => 1/2) 0 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : expectedAttempts (productTapes small 0) (tapeAttempt accepts) 0 = 0 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : expectedAttempts (productTapes small 3) (tapeAttempt (fun _ => false)) 3 = 3 :=
  by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : expectedAttempts (productTapes small 3) (tapeAttempt (fun _ => true)) 3 = 1 :=
  by decide +kernel

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem honest_single_rate : singleProbability (samples calls.toFinset 4) accepts = 3/32 := by
  rw [show accepts = candidateAccepted s msg calls raw from rfl,
    candidate_single_probability]
  decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (productTapes (samples calls.toFinset 4) 3).card = 16777216 := by
  rw [product_card, card_samples]
  decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : RetryBounds (productTapes (samples calls.toFinset 4) 3)
    (tapeAttempt accepts) (fun _ => 3/32) 3 := by
  rw [← honest_single_rate]
  exact product_retry_bounds _ (single_space_nonempty calls (by decide +kernel)) _ 3
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability (productTapes (samples calls.toFinset 4) 2)
    ((productTapes (samples calls.toFinset 4) 2).filter
      (fun w => (runProduct s msg calls raw 2 w).isOk = true)) = 183/1024 := by
  rw [candidate_product_extraction_probability s msg calls (by decide +kernel),
    ← candidate_single_probability, ← show accepts = candidateAccepted s msg calls raw from rfl,
    honest_single_rate]
  norm_num
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runProduct s msg calls raw 2 ![[1,1,3,4],calls]).isOk = true := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : runProduct s msg calls raw 2 ![[1,1,3,4],[1,1,3,4]] =
    .error "retryBudgetExhausted" := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : runProduct s msg calls raw 0 (fun i => Fin.elim0 i) =
    .error "retryBudgetExhausted" := by decide +kernel
set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ r, runProduct s msg calls raw 2 ![[1,1,3,4],calls] = .ok r ∧ ResultValid s r := by
  have h : (runProduct s msg calls raw 2 ![[1,1,3,4],calls]).isOk = true := by decide +kernel
  cases he : runProduct s msg calls raw 2 ![[1,1,3,4],calls] with
  | error e => simp [he, Except.isOk, Except.toBool] at h
  | ok r => exact ⟨r, rfl, runProduct_sound _ _ _ _ _ _ _ he⟩

end IPAProductTapeRegression

open IPAProductTapeRegression
open CryptoBulletproofsIPAProductTapeCandidateGeneratorContract
open CryptoBulletproofsIPABoundedRetryContract

set_option maxHeartbeats 6000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [
    decide ((productTapes small 1).card = 2),
    decide ((productTapes small 2).card = 4),
    decide ((productTapes small 3).card = 8),
    decide (singleProbability small accepts = 1/2),
    decide (expectedAttempts (productTapes small 3) (tapeAttempt accepts) 3 = 7/4),
    (runProduct s msg calls raw 2 ![[1,1,3,4],calls]).isOk,
    !(runProduct s msg calls raw 2 ![[1,1,3,4],[1,1,3,4]]).isOk,
    (candidate s msg calls raw calls).isSome,
    !(candidate s msg calls raw [1,1,3,4]).isSome,
    !(candidate (zs 1) zm calls absent calls).isSome,
    !(candidate (zs 1) zm calls wrongReply calls).isSome,
    !(candidate (zs 1) zm [0,1,2,3] zeroReply [0,1,2,3]).isSome,
    !(candidate (zs 1) zm [1,-1,2,3] zeroReply [1,-1,2,3]).isSome,
    decide (RetryBounds (productTapes small 3) (tapeAttempt accepts) (fun _ => 1/2) 3),
    decide (¬ RetryBounds small (fun _ w => accepts w) (fun _ => 1/2) 2),
    !(runProduct s msg calls raw 0 (fun i => Fin.elim0 i)).isOk]
  if checks.all id then IO.println s!"IPA_PRODUCT_TAPES_OK {checks.length}"
  else throw (IO.userError "product tape regression failed")

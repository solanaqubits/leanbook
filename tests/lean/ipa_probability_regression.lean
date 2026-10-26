/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAFiniteForkingProbabilityContract

namespace IPAProbabilityRegression
open CryptoBulletproofsIPAFiniteForkingProbabilityContract
open CryptoBulletproofsIPAForkingExtractionContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
set_option maxRecDepth 30000

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def six : Finset ℚ := {1,-1,2,-2,3,-3}
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def seven : Finset ℚ := insert 4 six

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : six.card = 6 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : seven.card = 7 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ x ∈ seven, x ≠ 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (successes six 4).card = 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : successProbability six six = 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (successes seven 4).card = 192 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : successProbability seven seven = 192 / 2401 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerCount 7 4 = 105 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerCount 5 4 = 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : lowerCount 6 4 = 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (samples seven 4).card = 2401 := by rw [card_samples]; decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : [1,2,3,4] ∈ successes seven 4 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : [1,-1,3,4] ∉ successes seven 4 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : [1,1,3,4] ∉ successes seven 4 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : [1,2,3,0] ∉ successes seven 4 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : IsFork seven ![1,2,3,4] := sampled_success_isFork seven 1 2 3 4 (by decide +kernel)
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < successProbability seven seven :=
  seven_probability_positive _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (105 : ℚ) / 2401 ≤ successProbability seven seven := by
  have h := fixed_prefix_probability_lower seven seven (by decide +kernel) (by decide +kernel)
  have hc : seven.card = 7 := by decide +kernel
  norm_num only [hc, Nat.cast_ofNat] at h ⊢
  exact h
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : successProbability seven (∅ : Finset ℚ) = 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : successProbability seven six = 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : successProbability seven seven ≤ 1 := probability_le_one (by decide +kernel) (by rfl)

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
/-- One high and one empty row: the mean is not a per-prefix guarantee. -/
def prefixes : Finset Bool := {false,true}
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def rows (b : Bool) : Finset ℚ := if b then seven else ∅
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def rates (b : Bool) : ℚ := rowRate seven (rows b)
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : average prefixes rates = 1/2 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rates false = 0 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rates true = 1 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : heavyFraction prefixes rates (1/3) = 1/2 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ ∀ b ∈ prefixes, (1/3 : ℚ) ≤ rates b := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((average prefixes rates - 1/3) / (1-1/3)) ≤ heavyFraction prefixes rates (1/3) :=
  heavy_prefix_fraction_lower _ (by decide +kernel) _ _ (by norm_num) (by decide +kernel)
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : average prefixes (fun b => successProbability seven (rows b)) = 96/2401
  := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rateBound 7 (6/7) = 0 := by norm_num [rateBound]
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < rateBound 7 (13/14) := rateBound_positive _ (by norm_num) _ (by norm_num)
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < average prefixes (fun _ => successProbability seven seven) := by
  apply average_forking_probability_positive prefixes (by decide +kernel) seven (by decide +kernel)
    (fun _ => seven) (by intros; rfl) (13/14) (by decide +kernel) (by norm_num)
  decide +kernel

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
/-- Fixed zero statement is a valid algebraic test, not a binding assumption. -/
def zeroStatement (k : ℕ) : Statement 101 (ZMod 101) k := ⟨0,0,0,0⟩
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroMessage : RoundMessages (ZMod 101) := ⟨0,0⟩
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def leafReply : IPATranscriptTree 101 (ZMod 101) 0 := .leaf (zeroStatement 0) 0 0
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls : List (ZMod 101) := [0,1,-1,2,-2,3,-3,4,5]
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def replies (x : ZMod 101) : Option (IPATranscriptTree 101 (ZMod 101) 0) :=
  if x = 5 then none else some leafReply

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem valid_replies (x : ZMod 101) (hx : x ≠ 0) (t : IPATranscriptTree 101 (ZMod 101) 0)
    (ht : replies x = some t) :
    ValidAcceptingTree (child_statement (zeroStatement 1) zeroMessage (Units.mk0 x hx)) t := by
  by_cases h5 : x = 5
  · simp [replies, h5] at ht
  · simp only [replies, if_neg h5, Option.some.injEq] at ht
    subst t
    have hg : fold_generators_G (Units.mk0 x hx) (0 : Vec 1 (ZMod 101)) = 0 := by
      funext i; simp [fold_generators_G, split_lo, split_hi]
    have hh : fold_generators_H (Units.mk0 x hx) (0 : Vec 1 (ZMod 101)) = 0 := by
      funext i; simp [fold_generators_H, split_lo, split_hi]
    simp [leafReply, zeroStatement, zeroMessage, ValidAcceptingTree, child_statement, hg, hh,
      update_target]

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (replySet calls replies).card = 7 := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 ∉ replySet calls replies := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 5 ∉ replySet calls replies := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < successProbability calls.toFinset (replySet calls replies) :=
  seven_probability_positive _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ t r, checked_extract (zeroStatement 1) t = .ok r ∧ ResultValid (zeroStatement 1) r :=
  positive_probability_extracts _ zeroMessage calls replies
    (seven_probability_positive _ _ (by decide +kernel) (by decide +kernel)) valid_replies
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : IsFork (replySet calls replies) ![1,2,3,4] := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ r, checked_extract (zeroStatement 1)
    (.node (zeroStatement 1) zeroMessage ![1,2,3,4] (fun _ => leafReply)) = .ok r ∧
    ResultValid (zeroStatement 1) r := by
  have he : (fun i : Fin 4 => (replies (![1,2,3,4] i)).getD (emptyTree 0)) =
      (fun _ => leafReply) := by
    funext i; fin_cases i <;> rfl
  simpa only [he] using sampled_fork_extracts (zeroStatement 1) zeroMessage calls replies
    ![1,2,3,4] (by decide +kernel) valid_replies

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
/-- A top-level reply may exist while its child context is false. Such an input
cannot satisfy the hypothesis needed by the probability/extraction bridge. -/
def badReply : IPATranscriptTree 101 (ZMod 101) 0 := .leaf { zeroStatement 0 with P := 1 } 0 0
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ ValidAcceptingTree (zeroStatement 0) badReply := by decide +kernel
set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checked_extract (zeroStatement 0) badReply = .error "invalidTree" := by decide +kernel

end IPAProbabilityRegression

open IPAProbabilityRegression CryptoBulletproofsIPAFiniteForkingProbabilityContract

set_option maxHeartbeats 4000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [
    decide ((successes six 4).card = 0),
    decide ((successes seven 4).card = 192),
    decide (successProbability seven seven = 192/2401),
    decide (successProbability seven six = 0),
    decide (lowerCount 7 4 = 105),
    decide ([1,2,3,4] ∈ successes seven 4),
    decide ([1,-1,3,4] ∉ successes seven 4),
    decide (average prefixes rates = 1/2),
    decide (heavyFraction prefixes rates (1/3) = 1/2),
    decide (average prefixes (fun b => successProbability seven (rows b)) = 96/2401),
    decide ((replySet calls replies).card = 7),
    decide (0 ∉ replySet calls replies),
    decide (5 ∉ replySet calls replies),
    decide (CryptoBulletproofsTreeExtraction.checked_extract (zeroStatement 0) badReply = .error
      "invalidTree")]
  if checks.all id then IO.println s!"IPA_PROBABILITY_OK {checks.length}"
  else throw (IO.userError "finite IPA probability regression failed")

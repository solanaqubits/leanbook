/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPATreeProbabilityContract

namespace IPATreeProbabilityRegression
open CryptoBulletproofsIPATreeProbabilityContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
set_option maxRecDepth 50000
set_option maxHeartbeats 6000000

def tapes : Finset Bool := {false, true}
def yes (w : Bool) : Bool := w
def no (w : Bool) : Bool := !w
example : probability tapes (passing tapes [yes]) = 1/2 := by decide +kernel
example : probability tapes (passing tapes [no]) = 1/2 := by decide +kernel
example : probability tapes (passing tapes [yes,no]) = 0 := by decide +kernel
example : ¬ ConditionalBounds tapes [yes,no] [1/2,1/2] := by decide +kernel
example : ConditionalBounds tapes [yes,no] [1/2,0] := by decide +kernel
example : ConditionalBounds tapes [yes,yes] [1/2,1] := by decide +kernel
example : probability tapes (passing tapes [yes,yes]) = 1/2 := by decide +kernel
example : (1/2 : ℚ) * (1/2) > probability tapes (passing tapes [yes,no]) := by decide +kernel
example : ConditionalBounds tapes [yes,no,yes] [1/2,0,1] := by decide +kernel
example : ¬ ConditionalBounds tapes [yes] [] := by decide +kernel
example : ¬ ConditionalBounds tapes [yes] [-1] := by decide +kernel
example : ¬ ConditionalBounds tapes [yes] [2] := by decide +kernel
example : (1/2 : ℚ) ≤ probability tapes (passing tapes [yes,yes]) := by
  simpa using sequential_probability_lower tapes (by decide +kernel) [yes,yes] [1/2,1]
    (by decide +kernel)
example : probability (∅ : Finset Bool) tapes = 0 := by decide +kernel
example : checkCount 0 = 1 := rfl
example : checkCount 1 = 5 := rfl
example : checkCount 2 = 21 := rfl
example : checkCount 3 = 85 := rfl

/-- Shrinking C while retaining A increases probability; N alone is not monotone. -/
def accepted : Finset ℚ := {1,2,3,4}
def enlarged : Finset ℚ := insert 5 accepted
def collapsed : Finset ℚ := {1,-1,2,-2}
example : CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability accepted accepted = 3/32 := by decide +kernel
example : CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability enlarged accepted = 24/625 := by decide +kernel
example : CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability enlarged accepted < CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability accepted accepted := by decide +kernel
example : CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability collapsed collapsed = 0 := by decide +kernel
example : accepted.card = collapsed.card := by decide +kernel
example : (CryptoBulletproofsIPAFiniteForkingProbabilityContract.successes ({1,-1,2,-2,3,-3} : Finset ℚ) 4).card = 0 := by decide +kernel

/-- All nonzero calls accepted: field7 has only three square classes; field11 has five. -/
instance : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 11) := ⟨by decide +kernel⟩
def field7 : Finset (ZMod 7) := Finset.univ.erase 0
def field11 : Finset (ZMod 11) := Finset.univ.erase 0
example : CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability field7 field7 = 0 := by decide +kernel
example : field11.card = 10 := by decide +kernel
example : 0 < CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability field11 field11 :=
  CryptoBulletproofsIPAFiniteForkingProbabilityContract.seven_probability_positive _ _
    (by decide +kernel) (by decide +kernel)

def zs (k : ℕ) : Statement 101 (ZMod 101) k := ⟨0,0,0,0⟩
def msg : RoundMessages (ZMod 101) := ⟨0,0⟩
def calls : List (ZMod 101) := [1,2,3,4]
def good : (k : ℕ) → IPATranscriptTree 101 (ZMod 101) k
  | 0 => .leaf (zs 0) 0 0
  | k + 1 => .node (zs (k + 1)) msg ![1,2,3,4] (fun _ => good k)
def badLeaf : IPATranscriptTree 101 (ZMod 101) 0 := .leaf { zs 0 with P := 1 } 0 0
/-- Root always valid, but sibling success events are disjoint on one shared bit. -/
def correlated (w : Bool) : IPATranscriptTree 101 (ZMod 101) 1 :=
  .node (zs 1) msg ![1,2,3,4] ![if w then good 0 else badLeaf,
    if w then badLeaf else good 0, good 0, good 0]

def depthTwo (w : Bool) : IPATranscriptTree 101 (ZMod 101) 2 :=
  if w then good 2 else .node (zs 2) msg ![1,2,3,4]
    ![good 1, good 1, good 1, .node (zs 1) msg ![1,2,3,4]
      ![good 0,good 0,good 0,badLeaf]]

example : ValidAcceptingTree (zs 0) (good 0) := by decide +kernel
example : ValidAcceptingTree (zs 1) (good 1) := by decide +kernel
example : ValidAcceptingTree (zs 2) (good 2) := by decide +kernel
example : leaf_count (good 2) = 16 := by decide +kernel
example : (localChecks (zs 2) (good 2)).length = 21 := localChecks_length _ _
example : ¬ ValidAcceptingTree (zs 0) badLeaf := by decide +kernel
example : ∀ w, ¬ ValidAcceptingTree (zs 1) (correlated w) := by decide +kernel
example : probability tapes (validOutcomes tapes (zs 1) correlated) = 0 := by decide +kernel
example : ∀ w, (localChecks (zs 1) (correlated w))[0]? = some true := by decide +kernel
example : probability tapes (validOutcomes tapes (zs 2) depthTwo) = 1/2 := by decide +kernel
example : (localChecks (zs 2) (depthTwo false))[20]? = some false := by decide +kernel
example : ConditionalBounds tapes (treeTests (zs 2) depthTwo)
    (List.replicate 20 1 ++ [1/2]) := by decide +kernel
example : (1/2 : ℚ) ≤ probability tapes (validOutcomes tapes (zs 2) depthTwo) := by
  have h := tree_probability_lower tapes (by decide +kernel) (zs 2) depthTwo
    (List.replicate 20 1 ++ [1/2]) (by decide +kernel)
  simpa using h
example : ∃ w ∈ tapes, ∃ r, checked_extract (zs 2) (depthTwo w) = .ok r ∧ ResultValid (zs 2) r :=
  positive_tree_probability_extracts tapes (zs 2) depthTwo (by decide +kernel)
example : (∃ a b : Vec 2 (ZMod 101), (zs 2).P = ipa_target (zs 2).U (zs 2).G (zs 2).H a b) ∨
    (∃ c, c ≠ 0 ∧ evaluate (zs 2) c = 0) :=
  conditional_tree_dichotomy tapes (by decide +kernel) (zs 2) depthTwo
    (List.replicate 20 1 ++ [1/2]) (by decide +kernel) (by norm_num)
example : passing tapes (treeTests (zs 1) correlated) = validOutcomes tapes (zs 1) correlated :=
  passing_treeTests _ _ _
example : tapes.filter (fun w => (checked_extract (zs 2) (depthTwo w)).isOk = true) =
    validOutcomes tapes (zs 2) depthTwo := extractor_event_eq _ _ _

def replies (_ : ZMod 101) : Option (IPATranscriptTree 101 (ZMod 101) 0) := some (good 0)
theorem children_valid (x : ZMod 101) (hx : x ≠ 0) (t : IPATranscriptTree 101 (ZMod 101) 0)
    (ht : replies x = some t) :
    ValidAcceptingTree (child_statement (zs 1) msg (Units.mk0 x hx)) t := by
  simp only [replies, Option.some.injEq] at ht
  subst t
  have hg : fold_generators_G (Units.mk0 x hx) (0 : Vec 1 (ZMod 101)) = 0 := by
    funext i; simp [fold_generators_G, split_lo, split_hi]
  have hh : fold_generators_H (Units.mk0 x hx) (0 : Vec 1 (ZMod 101)) = 0 := by
    funext i; simp [fold_generators_H, split_lo, split_hi]
  simp [good, zs, msg, ValidAcceptingTree, child_statement, hg, hh, update_target]

example : CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability calls.toFinset (CryptoBulletproofsIPAFiniteForkingProbabilityContract.replySet calls replies) ≤
    probability (CryptoBulletproofsIPAFiniteForkingProbabilityContract.samples calls.toFinset 4)
      (validOutcomes (CryptoBulletproofsIPAFiniteForkingProbabilityContract.samples calls.toFinset 4) (zs 1) (drawTree (zs 1) msg replies)) :=
  four_draw_tree_probability_lower _ _ calls replies children_valid
example : CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability calls.toFinset (CryptoBulletproofsIPAFiniteForkingProbabilityContract.replySet calls replies) = 3/32 := by decide +kernel
example : probability (CryptoBulletproofsIPAFiniteForkingProbabilityContract.samples calls.toFinset 4)
    (validOutcomes (CryptoBulletproofsIPAFiniteForkingProbabilityContract.samples calls.toFinset 4) (zs 1) (drawTree (zs 1) msg replies)) = 3/32 := by decide +kernel
example : checked_extract (zs 1) (drawTree (zs 1) msg replies [1,1,2,3]) = .error "invalidTree" := by decide +kernel
example : checked_extract (zs 1) (drawTree (zs 1) msg replies [1,2,3]) = .error "invalidTree" := by decide +kernel
example : checked_extract (zs 1) (drawTree (zs 1) msg replies [0,1,2,3]) = .error "invalidTree" := by decide +kernel
end IPATreeProbabilityRegression

open IPATreeProbabilityRegression CryptoBulletproofsIPATreeProbabilityContract
open CryptoBulletproofsTreeExtraction

def main : IO Unit := do
  let checks : List Bool := [
    decide (CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability field7 field7 = 0),
    decide (field11.card = 10),
    decide (probability tapes (passing tapes [yes,no]) = 0),
    decide (¬ ConditionalBounds tapes [yes,no] [1/2,1/2]),
    decide (ConditionalBounds tapes [yes,yes] [1/2,1]),
    decide (ConditionalBounds tapes [yes,no,yes] [1/2,0,1]),
    decide (CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability enlarged accepted < CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability accepted accepted),
    decide (CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability collapsed collapsed = 0),
    decide (ValidAcceptingTree (zs 2) (good 2)),
    decide (leaf_count (good 2) = 16),
    decide (probability tapes (validOutcomes tapes (zs 1) correlated) = 0),
    decide (probability tapes (validOutcomes tapes (zs 2) depthTwo) = 1/2),
    decide (ConditionalBounds tapes (treeTests (zs 2) depthTwo) (List.replicate 20 1 ++ [1/2])),
    decide (checked_extract (zs 0) badLeaf = .error "invalidTree"),
    decide (checked_extract (zs 1) (drawTree (zs 1) msg replies [1,1,2,3]) = .error "invalidTree"),
    decide (checked_extract (zs 1) (drawTree (zs 1) msg replies [1,2,3]) = .error "invalidTree"),
    decide (checked_extract (zs 1) (drawTree (zs 1) msg replies [0,1,2,3]) = .error "invalidTree"),
    decide (CryptoBulletproofsIPAFiniteForkingProbabilityContract.successProbability calls.toFinset (CryptoBulletproofsIPAFiniteForkingProbabilityContract.replySet calls replies) = 3/32)]
  if checks.all id then IO.println s!"IPA_TREE_PROBABILITY_OK {checks.length}"
  else throw (IO.userError "IPA tree probability regression failed")

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAPublicScalarBindingContract

namespace IPAPublicScalarRegression
open CryptoBulletproofsIPAPublicScalarBindingContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
namespace C
export CryptoBulletproofsIPAPublicScalarBindingContract.Counterexample
  (claim eta₀ eta₁ first second relation)
end C
set_option maxRecDepth 50000

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def units := CryptoBulletproofsWitnessExtraction.Examples.units
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def e₀ : (ZMod 101)ˣ := 1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def e₁ : (ZMod 101)ˣ := Units.mk0 (2 : ZMod 101) (by decide)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def eneg : (ZMod 101)ˣ := -1

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def G := CryptoBulletproofsTreeExtraction.Examples.G
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def H := CryptoBulletproofsTreeExtraction.Examples.H
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def a := CryptoBulletproofsTreeExtraction.Examples.a
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def b := CryptoBulletproofsTreeExtraction.Examples.b
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def publicClaim (k : ℕ) := honestClaim (17 : ZMod 101) (G k) (H k) (a k) (b k)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def tree (k : ℕ) (η : (ZMod 101)ˣ) :=
  honestTree units ((η : ZMod 101) • (17 : ZMod 101)) (G k) (H k) (a k) (b k)

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem honest_all_depths (k : ℕ) :
    checkedPair (publicClaim k) e₀ e₁ (tree k e₀) (tree k e₁) = .ok (.witness (a k) (b k)) :=
  checkedPair_honest units (by decide +kernel) _ _ _ _ _ _ _ (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair (publicClaim 1) e₀ e₁ (tree 1 e₀) (tree 1 e₁) =
    .ok (.witness (a 1) (b 1)) := honest_all_depths 1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair (publicClaim 2) e₀ e₁ (tree 2 e₀) (tree 2 e₁) =
    .ok (.witness (a 2) (b 2)) := honest_all_depths 2
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : leaf_count (tree 1 e₀) = 4 := tree_leaf_count_eq _
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : leaf_count (tree 2 e₁) = 16 := tree_leaf_count_eq _
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : WitnessValid (publicClaim 2) (a 2) (b 2) := ⟨rfl, rfl⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ClaimResultValid (publicClaim 2) (.witness (a 2) (b 2)) :=
  checkedPair_sound _ _ _ _ _ _ (honest_all_depths 2)

-- Outer challenges need only be distinct, not have distinct squares.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (e₀ : ZMod 101)^2 = (eneg : ZMod 101)^2 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : e₀ ≠ eneg := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair (publicClaim 1) e₀ eneg (tree 1 e₀) (tree 1 eneg) =
    .ok (.witness (a 1) (b 1)) :=
  checkedPair_honest units (by decide +kernel) _ _ _ _ _ _ _ (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ValidAcceptingTree (toIPA C.claim C.eta₀) C.first := Counterexample.first_valid
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ValidAcceptingTree (toIPA C.claim C.eta₁) C.second := Counterexample.second_valid
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬∃ a b, WitnessValid C.claim a b := Counterexample.no_public_witness
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (extractTree C.first) = .witness 0 0 := rfl
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair C.claim C.eta₀ C.eta₁ C.first C.second = .ok (.relation C.relation) :=
  Counterexample.checked_relation
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : difference C.claim C.eta₀ C.eta₁ 0 0 (fun _ => 1) 0 = C.relation := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : C.relation.1 0 = -1 := rfl
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : C.relation.2.1 0 = 0 := rfl
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : C.relation.2.2 = 1 := rfl
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : C.relation ≠ 0 := Counterexample.explicit_relation.1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : evaluate (baseStatement C.claim) C.relation = 0 := Counterexample.explicit_relation.2
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair C.claim C.eta₀ C.eta₀ C.first C.first = .error "invalidOuterFork" :=
  checkedPair_diagonal _ _ _ _
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : difference C.claim C.eta₀ C.eta₀ 0 0 0 0 = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : dot_product (0 : Vec 0 (ZMod 5)) 0 ≠ C.claim.c := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ClaimResultValid C.claim (extractPair C.claim C.eta₀ C.eta₀ C.first C.first) :=
  Counterexample.diagonal_raw_wrong.2

-- Three distinct context mismatches; no blanket syntax-change rejection claim.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongQ : PublicClaim 5 (ZMod 5) 0 := { C.claim with Q := 0 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongC : PublicClaim 5 (ZMod 5) 0 := { C.claim with c := 2 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongU : PublicClaim 5 (ZMod 5) 0 := { C.claim with U := 2 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair wrongQ C.eta₀ C.eta₁ C.first C.second = .error "invalidOuterFork" :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair wrongC C.eta₀ C.eta₁ C.first C.second = .error "invalidOuterFork" :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair wrongU C.eta₀ C.eta₁ C.first C.second = .error "invalidOuterFork" :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedPair C.claim C.eta₀ C.eta₁ C.second C.first = .error "invalidOuterFork" :=
  by decide +kernel

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroU : PublicClaim 5 (ZMod 5) 0 := { C.claim with U := 0 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : toIPA zeroU C.eta₀ = toIPA { zeroU with c := 2 } C.eta₀ := by decide +kernel

-- Scaling and both existing relation branches, including a nonzero U coefficient.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def uRelation : GeneratorCoefficients 5 0 := (0, 0, 1)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : liftRelation C.eta₁ uRelation = (0, 0, 2) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : liftRelation C.eta₁ uRelation ≠ 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : evaluate (baseStatement zeroU) (liftRelation C.eta₁ uRelation) = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : liftRelation C.eta₁ C.relation ≠ 0 := liftRelation_nonzero _ _
  Counterexample.explicit_relation.1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : evaluate (baseStatement C.claim) (liftRelation C.eta₁ C.relation) =
    evaluate (toIPA C.claim C.eta₁) C.relation := liftRelation_eval _ _ _
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : combineResults zeroU C.eta₀ C.eta₁ (.relation uRelation) (.witness 0 0) =
    .relation uRelation := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : combineResults zeroU C.eta₀ C.eta₁ (.witness 0 0) (.relation uRelation) =
    .relation (0, 0, 2) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ClaimResultValid zeroU (combineResults zeroU C.eta₀ C.eta₁
    (.relation uRelation) (.relation uRelation)) :=
  combineResults_sound _ _ _ (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedPair C.claim C.eta₀ C.eta₁ C.first C.second).isOk = true ↔
    ValidFork C.claim C.eta₀ C.eta₁ C.first C.second := checkedPair_success_iff _ _ _ _ _

end IPAPublicScalarRegression
open IPAPublicScalarRegression
open CryptoBulletproofsIPAPublicScalarBindingContract CryptoBulletproofsTreeExtraction

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks := [
    decide (checkedPair (publicClaim 1) e₀ e₁ (tree 1 e₀) (tree 1 e₁) = .ok (.witness (a 1) (b 1))),
    decide (checkedPair (publicClaim 2) e₀ e₁ (tree 2 e₀) (tree 2 e₁) = .ok (.witness (a 2) (b 2))),
    decide (checkedPair (publicClaim 1) e₀ eneg (tree 1 e₀) (tree 1 eneg) = .ok (.witness (a 1) (b
      1))),
    decide (leaf_count (tree 2 e₀) = 16),
    decide (checkedPair C.claim C.eta₀ C.eta₁ C.first C.second = .ok (.relation C.relation)),
    decide (C.relation ≠ 0),
    decide (evaluate (baseStatement C.claim) C.relation = 0),
    decide (checkedPair C.claim C.eta₀ C.eta₀ C.first C.first = .error "invalidOuterFork"),
    decide (checkedPair wrongQ C.eta₀ C.eta₁ C.first C.second = .error "invalidOuterFork"),
    decide (checkedPair wrongC C.eta₀ C.eta₁ C.first C.second = .error "invalidOuterFork"),
    decide (checkedPair wrongU C.eta₀ C.eta₁ C.first C.second = .error "invalidOuterFork"),
    decide (checkedPair C.claim C.eta₀ C.eta₁ C.second C.first = .error "invalidOuterFork"),
    decide (liftRelation C.eta₁ uRelation = (0, 0, 2)),
    decide (toIPA zeroU C.eta₀ = toIPA { zeroU with c := 2 } C.eta₀),
    decide (ClaimResultValid zeroU (combineResults zeroU C.eta₀ C.eta₁
      (.relation uRelation) (.relation uRelation))),
    decide (¬∃ a b, WitnessValid C.claim a b)]
  unless checks.all id do throw (IO.userError "publicClaim scalar binding regression failed")
  IO.println s!"IPA_PUBLIC_SCALAR_OK {checks.length}"

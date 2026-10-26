/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAPedersenOpeningConsistencyContract
namespace IPAPedersenRegression
open CryptoBulletproofsIPAPedersenOpeningConsistencyContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
set_option maxRecDepth 50000
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace C
export CryptoBulletproofsIPAPublicScalarBindingContract.Counterexample
  (claim eta₀ eta₁ first second relation)
end C

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def units := CryptoBulletproofsWitnessExtraction.Examples.units
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def eta₀ : (ZMod 101)ˣ := 1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def eta₁ : (ZMod 101)ˣ := Units.mk0 (2 : ZMod 101) (by decide)
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
def gens (k : ℕ) : Range.Generators 101 (ZMod 101) k := ⟨7, 13, 17, G k, H k⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def claim (k : ℕ) := honestClaim (gens k) (a k) (b k) 9
-- A zero OPENING challenge is allowed; IPA outer challenges remain units.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def bundle (k : ℕ) := honestBundle (gens k) (a k) (b k) 9 (4, 6) 0 3 eta₀ eta₁ units

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem honest_all_depths (k : ℕ) : checkedBundle (claim k) (bundle k) =
    .ok (.witness ⟨a k, b k, dot_product (a k) (b k), 9⟩) :=
  checkedBundle_honest _ _ _ _ _ _ _ (by decide +kernel) _ _ (by decide +kernel)
    _ (by decide +kernel)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ResultValid (claim 2) (.witness ⟨a 2, b 2, dot_product (a 2) (b 2), 9⟩) :=
  checkedBundle_sound _ _ _ (honest_all_depths 2)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle (claim 1) (bundle 1) =
    .ok (.witness ⟨a 1, b 1, dot_product (a 1) (b 1), 9⟩) := honest_all_depths 1
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle (claim 2) (bundle 2) =
    .ok (.witness ⟨a 2, b 2, dot_product (a 2) (b 2), 9⟩) := honest_all_depths 2
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : leaf_count (bundle 2).tree₀ = 16 := tree_leaf_count_eq _

-- F5, depth zero: force the genuine relation branch from epsilon211.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def small : CommittedClaim 5 (ZMod 5) 0 := ⟨⟨2, 3, 1, fun _ => 1, fun _ => 1⟩, 4, 3⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def op (e : ZMod 5) := Opening.honestTranscript (Opening.scalarMap (2 : ZMod 5) 3) (1, 2) (3, 4) e
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def relBundle : ForkBundle 5 (ZMod 5) 0 := ⟨op 0, op 1, C.eta₀, C.eta₁, C.first, C.second⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def rel : Range.RelationCoefficients 5 0 := liftRelation C.relation

-- Independently valid opening of the SAME V, but c=2 rather than c=1.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def otherOp (e : ZMod 5) := Opening.honestTranscript (Opening.scalarMap (2 : ZMod 5) 3) (2, 3) (3,
  4) e
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def mismatch : ForkBundle 5 (ZMod 5) 0 :=
  { relBundle with opening₀ := otherOp 0, opening₁ := otherOp 1 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badAnnouncement := { relBundle with opening₁ := { op 1 with announcement := 0 } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badResponse := { relBundle with opening₁ := { op 1 with response := (0,0) } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badStatement := { relBundle with opening₁ := { op 1 with statement := 4 } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def equalOpening := { relBundle with opening₁ := op 0 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def equalIPA := { relBundle with eta₁ := C.eta₀ }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongQ : CommittedClaim 5 (ZMod 5) 0 := { small with Q := 0 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongV : CommittedClaim 5 (ZMod 5) 0 := { small with V := 0 }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def swapped := { relBundle with tree₀ := C.second, tree₁ := C.first }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def collisionRelation : Range.RelationCoefficients 5 0 := ⟨0, 0, 1-2, 2-3, 0⟩
-- Finite counterexample: H != 0 in F5^2 does not make its scalar map surjective.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def vectorH : ZMod 5 × ZMod 5 := (1,0)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def vectorG : ZMod 5 × ZMod 5 := (0,1)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (r c : ZMod 5) : (c • vectorG + r • vectorH).2 = c := by simp [vectorG, vectorH]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ValidBundle small relBundle := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : opening relBundle = (1,2) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small relBundle = .ok (.relation rel) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ResultValid small (.relation rel) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rel ≠ 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Range.relation_eval small.generators rel = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : rel.base = 0 ∧ rel.blind = 0 ∧ rel.ipa = 1 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬∃ a b, WitnessValid small ⟨a,b,1,2⟩ := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : WitnessValid small ⟨0, (fun _ => 4), 0, 1⟩ := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : OpeningValid small mismatch := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : opening mismatch = (2,3) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ValidBundle small mismatch := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small mismatch = .error .invalidIPAFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small badAnnouncement = .error .invalidOpeningFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small badResponse = .error .invalidOpeningFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small badStatement = .error .invalidOpeningFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small equalOpening = .error .invalidOpeningFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small equalIPA = .error .invalidIPAFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle wrongQ relBundle = .error .invalidIPAFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle wrongV relBundle = .error .invalidOpeningFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedBundle small swapped = .error .invalidIPAFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : collisionRelation ≠ 0 ∧ Range.relation_eval small.generators collisionRelation = 0
  := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : vectorH ≠ 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬Function.Surjective (fun r : ZMod 5 => r • vectorH) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1 : ZMod 5) • (1 : ZMod 5) + 2 • (1 : ZMod 5) = 2 • (1 : ZMod 5) + 1 • (1 : ZMod 5)
  := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (d : GeneratorCoefficients 101 2) (hd : d ≠ 0) : liftRelation d ≠ 0 := liftRelation_nonzero
  _ hd
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (f : ForkBundle 101 (ZMod 101) 2) (h : ValidBundle (claim 2) f) :
    ResultValid (claim 2) (extractBundle (claim 2) f) := bundle_extraction_soundness _ _ h
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedBundle small relBundle = .ok (.relation rel)) ↔
    ValidBundle small relBundle ∧ extractBundle small relBundle = .relation rel
      := checkedBundle_success_iff _ _ _
end IPAPedersenRegression
open IPAPedersenRegression CryptoBulletproofsIPAPedersenOpeningConsistencyContract
open CryptoBulletproofsInnerProduct

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks := [
    decide (ValidBundle small relBundle),
    decide (opening relBundle = (1,2)),
    decide (checkedBundle small relBundle = .ok (.relation rel)),
    decide (ResultValid small (.relation rel)),
    decide (rel ≠ 0),
    decide (Range.relation_eval small.generators rel = 0),
    decide (rel.base = 0 ∧ rel.blind = 0 ∧ rel.ipa = 1),
    decide (¬∃ a b, WitnessValid small ⟨a,b,1,2⟩),
    decide (WitnessValid small ⟨0, (fun _ => 4), 0, 1⟩),
    decide (OpeningValid small mismatch),
    decide (opening mismatch = (2,3)),
    decide (¬ValidBundle small mismatch),
    decide (checkedBundle small mismatch = .error .invalidIPAFork),
    decide (checkedBundle small badAnnouncement = .error .invalidOpeningFork),
    decide (checkedBundle small badResponse = .error .invalidOpeningFork),
    decide (checkedBundle small badStatement = .error .invalidOpeningFork),
    decide (checkedBundle small equalOpening = .error .invalidOpeningFork),
    decide (checkedBundle small equalIPA = .error .invalidIPAFork),
    decide (checkedBundle wrongQ relBundle = .error .invalidIPAFork),
    decide (checkedBundle wrongV relBundle = .error .invalidOpeningFork),
    decide (checkedBundle small swapped = .error .invalidIPAFork),
    decide (collisionRelation ≠ 0 ∧ Range.relation_eval small.generators collisionRelation = 0),
    decide (vectorH ≠ 0),
    decide (¬Function.Surjective (fun r : ZMod 5 => r • vectorH)),
    decide ((1 : ZMod 5) • (1 : ZMod 5) + 2 • (1 : ZMod 5) = 2 • (1 : ZMod 5) + 1 • (1 : ZMod 5)),
    decide (checkedBundle (claim 1) (bundle 1) = .ok (.witness ⟨a 1, b 1, dot_product (a 1) (b 1),
      9⟩)),
    decide (checkedBundle (claim 2) (bundle 2) = .ok (.witness ⟨a 2, b 2, dot_product (a 2) (b 2),
      9⟩))]
  unless checks.all id do throw (IO.userError "Pedersen/IPA consistency regression failed")
  IO.println s!"IPA_PEDERSEN_CONSISTENCY_OK {checks.length}"

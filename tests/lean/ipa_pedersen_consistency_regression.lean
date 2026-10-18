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
set_option maxHeartbeats 8000000
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
namespace C
export CryptoBulletproofsIPAPublicScalarBindingContract.Counterexample
  (claim eta₀ eta₁ first second relation)
end C

def units := CryptoBulletproofsWitnessExtraction.Examples.units
def eta₀ : (ZMod 101)ˣ := 1
def eta₁ : (ZMod 101)ˣ := Units.mk0 (2 : ZMod 101) (by decide)
def G := CryptoBulletproofsTreeExtraction.Examples.G
def H := CryptoBulletproofsTreeExtraction.Examples.H
def a := CryptoBulletproofsTreeExtraction.Examples.a
def b := CryptoBulletproofsTreeExtraction.Examples.b
def gens (k : ℕ) : Range.Generators 101 (ZMod 101) k := ⟨7, 13, 17, G k, H k⟩
def claim (k : ℕ) := honestClaim (gens k) (a k) (b k) 9
-- A zero OPENING challenge is allowed; IPA outer challenges remain units.
def bundle (k : ℕ) := honestBundle (gens k) (a k) (b k) 9 (4, 6) 0 3 eta₀ eta₁ units

theorem honest_all_depths (k : ℕ) : checkedBundle (claim k) (bundle k) =
    .ok (.witness ⟨a k, b k, dot_product (a k) (b k), 9⟩) :=
  checkedBundle_honest _ _ _ _ _ _ _ (by decide +kernel) _ _ (by decide +kernel)
    _ (by decide +kernel)
example : ResultValid (claim 2) (.witness ⟨a 2, b 2, dot_product (a 2) (b 2), 9⟩) :=
  checkedBundle_sound _ _ _ (honest_all_depths 2)
example : checkedBundle (claim 1) (bundle 1) =
    .ok (.witness ⟨a 1, b 1, dot_product (a 1) (b 1), 9⟩) := honest_all_depths 1
example : checkedBundle (claim 2) (bundle 2) =
    .ok (.witness ⟨a 2, b 2, dot_product (a 2) (b 2), 9⟩) := honest_all_depths 2
example : leaf_count (bundle 2).tree₀ = 16 := tree_leaf_count_eq _

-- F5, depth zero: force the genuine relation branch from epsilon211.
def small : CommittedClaim 5 (ZMod 5) 0 := ⟨⟨2, 3, 1, fun _ => 1, fun _ => 1⟩, 4, 3⟩
def op (e : ZMod 5) := Opening.honestTranscript (Opening.scalarMap (2 : ZMod 5) 3) (1, 2) (3, 4) e
def relBundle : ForkBundle 5 (ZMod 5) 0 := ⟨op 0, op 1, C.eta₀, C.eta₁, C.first, C.second⟩
def rel : Range.RelationCoefficients 5 0 := liftRelation C.relation

-- Independently valid opening of the SAME V, but c=2 rather than c=1.
def otherOp (e : ZMod 5) := Opening.honestTranscript (Opening.scalarMap (2 : ZMod 5) 3) (2, 3) (3, 4) e
def mismatch : ForkBundle 5 (ZMod 5) 0 := { relBundle with opening₀ := otherOp 0, opening₁ := otherOp 1 }
def badAnnouncement := { relBundle with opening₁ := { op 1 with announcement := 0 } }
def badResponse := { relBundle with opening₁ := { op 1 with response := (0,0) } }
def badStatement := { relBundle with opening₁ := { op 1 with statement := 4 } }
def equalOpening := { relBundle with opening₁ := op 0 }
def equalIPA := { relBundle with eta₁ := C.eta₀ }
def wrongQ : CommittedClaim 5 (ZMod 5) 0 := { small with Q := 0 }
def wrongV : CommittedClaim 5 (ZMod 5) 0 := { small with V := 0 }
def swapped := { relBundle with tree₀ := C.second, tree₁ := C.first }
def collisionRelation : Range.RelationCoefficients 5 0 := ⟨0, 0, 1-2, 2-3, 0⟩
-- Finite counterexample: H != 0 in F5^2 does not make its scalar map surjective.
def vectorH : ZMod 5 × ZMod 5 := (1,0)
def vectorG : ZMod 5 × ZMod 5 := (0,1)
example (r c : ZMod 5) : (c • vectorG + r • vectorH).2 = c := by simp [vectorG, vectorH]
example : ValidBundle small relBundle := by decide +kernel
example : opening relBundle = (1,2) := by decide +kernel
example : checkedBundle small relBundle = .ok (.relation rel) := by decide +kernel
example : ResultValid small (.relation rel) := by decide +kernel
example : rel ≠ 0 := by decide +kernel
example : Range.relation_eval small.generators rel = 0 := by decide +kernel
example : rel.base = 0 ∧ rel.blind = 0 ∧ rel.ipa = 1 := by decide +kernel
example : ¬∃ a b, WitnessValid small ⟨a,b,1,2⟩ := by decide +kernel
example : WitnessValid small ⟨0, (fun _ => 4), 0, 1⟩ := by decide +kernel
example : OpeningValid small mismatch := by decide +kernel
example : opening mismatch = (2,3) := by decide +kernel
example : ¬ValidBundle small mismatch := by decide +kernel
example : checkedBundle small mismatch = .error .invalidIPAFork := by decide +kernel
example : checkedBundle small badAnnouncement = .error .invalidOpeningFork := by decide +kernel
example : checkedBundle small badResponse = .error .invalidOpeningFork := by decide +kernel
example : checkedBundle small badStatement = .error .invalidOpeningFork := by decide +kernel
example : checkedBundle small equalOpening = .error .invalidOpeningFork := by decide +kernel
example : checkedBundle small equalIPA = .error .invalidIPAFork := by decide +kernel
example : checkedBundle wrongQ relBundle = .error .invalidIPAFork := by decide +kernel
example : checkedBundle wrongV relBundle = .error .invalidOpeningFork := by decide +kernel
example : checkedBundle small swapped = .error .invalidIPAFork := by decide +kernel
example : collisionRelation ≠ 0 ∧ Range.relation_eval small.generators collisionRelation = 0 := by decide +kernel
example : vectorH ≠ 0 := by decide +kernel
example : ¬Function.Surjective (fun r : ZMod 5 => r • vectorH) := by decide +kernel
example : (1 : ZMod 5) • (1 : ZMod 5) + 2 • (1 : ZMod 5) = 2 • (1 : ZMod 5) + 1 • (1 : ZMod 5) := by decide +kernel
example (d : GeneratorCoefficients 101 2) (hd : d ≠ 0) : liftRelation d ≠ 0 := liftRelation_nonzero _ hd
example (f : ForkBundle 101 (ZMod 101) 2) (h : ValidBundle (claim 2) f) :
    ResultValid (claim 2) (extractBundle (claim 2) f) := bundle_extraction_soundness _ _ h
example : (checkedBundle small relBundle = .ok (.relation rel)) ↔
    ValidBundle small relBundle ∧ extractBundle small relBundle = .relation rel := checkedBundle_success_iff _ _ _
end IPAPedersenRegression
open IPAPedersenRegression CryptoBulletproofsIPAPedersenOpeningConsistencyContract
open CryptoBulletproofsInnerProduct

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
    decide (checkedBundle (claim 1) (bundle 1) = .ok (.witness ⟨a 1, b 1, dot_product (a 1) (b 1), 9⟩)),
    decide (checkedBundle (claim 2) (bundle 2) = .ok (.witness ⟨a 2, b 2, dot_product (a 2) (b 2), 9⟩))]
  unless checks.all id do throw (IO.userError "Pedersen/IPA consistency regression failed")
  IO.println s!"IPA_PEDERSEN_CONSISTENCY_OK {checks.length}"

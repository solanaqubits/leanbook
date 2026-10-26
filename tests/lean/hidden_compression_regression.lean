import Verification.CryptoHiddenScalarInnerProductCompressionContract
namespace HiddenCompressionRegression
open CryptoHiddenScalarInnerProductCompressionContract CryptoBulletproofsInnerProduct
open CryptoBulletproofsTreeExtraction
namespace H
export CryptoHiddenScalarInnerProductProtocolContract
  (Witness Claim MaskRandomness honestTranscript WitnessValid honest_fork_valid Transcript
   realView seededSimView honestInteraction ResultValid ValidFork)
namespace Range
export CryptoBulletproofsRangeReduction (Generators)
export CryptoBulletproofsRangeWitnessExtraction (RelationCoefficients relation_eval)
end Range
end H
namespace P.Counterexample
export CryptoBulletproofsIPAPublicScalarBindingContract.Counterexample
  (eta₀ eta₁ first second relation)
end P.Counterexample
namespace C
export CryptoBulletproofsIPAPedersenOpeningConsistencyContract (liftRelation)
end C
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
set_option maxRecDepth 20000
abbrev F := ZMod 11

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def units : Fin 4 → Fˣ := ![1, Units.mk0 2 (by decide),
  Units.mk0 3 (by decide), Units.mk0 4 (by decide)]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def gens (k : ℕ) : H.Range.Generators 11 F k := ⟨1,2,3,fun _ => 1,fun _ => 1⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def witness (k : ℕ) : H.Witness 11 k := ⟨fun _ => 1,fun _ => 2,1⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def claim (k : ℕ) : H.Claim 11 F k :=
  ⟨gens k, multiscalar_mul (witness k).a (gens k).G + multiscalar_mul (witness k).b (gens k).H,
   dot_product (witness k).a (witness k).b • (gens k).B + (witness k).rho • (gens k).Hblind⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def masks (k : ℕ) : H.MaskRandomness 11 k := (fun _ => 1,fun _ => 2,3,4)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def full (k : ℕ) (e : F) := H.honestTranscript (claim k) (witness k) (masks k) e
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls (k : ℕ) : Challenges 11 k := (units 1,fun _ => units 2)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wire (k : ℕ) (e : F) := compress (claim k) (full k e) (calls k)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def fork (k : ℕ) := forkFromFull (claim k) (fun i : Fin 3 => full k i.val) units (units 0) (units 1)

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem witness_valid (k : ℕ) : H.WitnessValid (claim k) (witness k) := ⟨rfl,rfl⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem full_valid (k : ℕ) : H.ValidFork (claim k) (fun i : Fin 3 => full k i.val) :=
  H.honest_fork_valid _ _ (witness_valid k) (masks k)
    (fun i : Fin 3 => (i.val : F)) (by decide +kernel)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem all_forks_valid (k : ℕ) : ValidCompressedFork (claim k) (fork k) :=
  fork_from_full_valid _ _
    (H.honest_fork_valid _ _ (witness_valid k) _ _ (by decide +kernel))
    units (by decide +kernel) _ _ (by decide +kernel)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Function.Injective (fun i => (units i : F)^2) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : compressedVerify (claim 0) (wire 0 0) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : compressedVerify (claim 1) (wire 1 0) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : compressedVerify (claim 2) (wire 2 2) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 0) (fork 0) = some (.witness (witness 0)) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 1) (fork 1) = some (.witness (witness 1)) := by
  rw [checkedExtract, if_pos (all_forks_valid 1)]
  rw [fork, extract_from_full _ _ (full_valid 1) units (by decide +kernel)]
  decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 2) (fork 2) = some (.witness (witness 2)) := by
  rw [checkedExtract, if_pos (all_forks_valid 2)]
  rw [fork, extract_from_full _ _ (full_valid 2) units (by decide +kernel)]
  decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (wire 2 0).product = dot_product (masks 2).1 (masks 2).2.1 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (group_payload (wire 2 0).proof).length = 4 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (scalar_payload (wire 2 0).proof).length = 2 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : leaf_count ((fork 2).nodes 0).tree₀ = 16 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (wire 1 0).product = (compress (claim 1) (full 1 0) (1,fun _ => 1)).product := rfl
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (wire 1 0).blind = (compress (claim 1) (full 1 0) (1,fun _ => 1)).blind := rfl
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((compress (claim 2) (full 2 1) (1,![units 0,units 1])).proof).rounds 1 =
    ((compress (claim 2) (full 2 1) (1,![units 0,units 2])).proof).rounds 1 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((compress (claim 2) (full 2 1) (1,![units 0,units 1])).proof).rounds 0 =
    ((compress (claim 2) (full 2 1) (1,![units 2,units 3])).proof).rounds 0 := by decide +kernel

-- Outer extraction relation, while all six IPA trees give exact vector witnesses.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def relClaim : H.Claim 11 F 0 := ⟨⟨1,1,1,fun _ => 1,fun _ => 1⟩,0,0⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def relFull : Fin 3 → H.Transcript 11 F 0 :=
  ![⟨⟨0,0,0⟩,0,⟨0,0,0⟩⟩,⟨⟨0,0,0⟩,1,⟨0,0,0⟩⟩,
    ⟨⟨0,0,0⟩,2,⟨fun _ => 1,fun _ => 10,1⟩⟩]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerFork := forkFromFull relClaim relFull units (units 0) (units 1)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerRelation : H.Range.RelationCoefficients 11 0 := ⟨fun _ => 1,fun _ => 10,0,0,0⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ValidCompressedFork relClaim outerFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract relClaim outerFork = some (.relation outerRelation) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ i, isRelation (nodeResult relClaim outerFork i) = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : outerRelation ≠ 0 ∧ H.Range.relation_eval relClaim.generators outerRelation = 0 :=
  by decide +kernel

-- Inner public-scalar relation at depth zero; no four-square fork claimed over F5.
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def innerClaim : H.Claim 5 (ZMod 5) 0 := ⟨⟨1,1,1,fun _ => 1,fun _ => 1⟩,0,0⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def innerFork : CompressedFork 5 (ZMod 5) 0 :=
  ⟨⟨4,1,0⟩, fun i => ⟨i.val,1,0,P.Counterexample.eta₀,P.Counterexample.eta₁,
    P.Counterexample.first,P.Counterexample.second⟩⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def innerRelation := C.liftRelation P.Counterexample.relation
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ValidCompressedFork innerClaim innerFork := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract innerClaim innerFork = some (.relation innerRelation) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : isRelation (nodeResult innerClaim innerFork 0) = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : innerRelation ≠ 0 ∧ H.Range.relation_eval innerClaim.generators innerRelation = 0 :=
  by decide +kernel

-- Rejection means a failed predicate, not syntactic inequality alone.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badOuter := { fork 1 with nodes := fun i => { (fork 1).nodes i with challenge := 0 } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badEta := { fork 1 with nodes := fun i =>
  { (fork 1).nodes i with eta₁ := ((fork 1).nodes i).eta₀ } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badT := { fork 1 with nodes := fun i =>
  { (fork 1).nodes i with product := ((fork 1).nodes i).product + 1 } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badZ := { fork 1 with nodes := fun i =>
  { (fork 1).nodes i with blind := ((fork 1).nodes i).blind + 1 } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badAnn := { fork 1 with announcement := { (fork 1).announcement with mask := 0 } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badTree := { fork 1 with nodes := fun i =>
  { (fork 1).nodes i with tree₀ := ((fork 1).nodes i).tree₁ } }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 1) badOuter = none := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 1) badEta = none := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 1) badT = none := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 1) badZ = none := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 1) badAnn = none := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedExtract (claim 1) badTree = none := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ compressedVerify (claim 1) { wire 1 1 with product := 0 } := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ compressedVerify { claim 1 with P := 0 } (wire 1 1) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ compressedVerify { claim 1 with V := 0 } (wire 1 1) := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : compressedVerify { claim 1 with P := 0, V := 0 } (wire 1 0) := by decide +kernel

-- Exact laws, instantiated separately from executable finite scenarios.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem blinding (k : ℕ) : Function.Bijective (fun x : F => x • (claim k).generators.Hblind) :=
  CryptoPedersenHomomorphicSum.nonzero_generator_bijective
    (CryptoPedersenHomomorphicSum.scalarSetup 2 (by decide)) (by change (2 : F) ≠ 0; decide)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (k : ℕ) (e : F) (mu : PMF (Challenges 11 k)) :
    (H.realView (claim k) (witness k) e).bind (compressionKernel (claim k) mu) =
      (H.seededSimView (claim k) e).bind (compressionKernel (claim k) mu) :=
  compressed_hvzk _ _ (witness_valid k) (blinding k) e mu
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (k : ℕ) :
    honestExecution (claim k) (witness k) (PMF.uniformOfFintype _) (PMF.uniformOfFintype _)
      (PMF.uniformOfFintype _) = simulatedExecution (claim k) (PMF.uniformOfFintype _)
        (uniformChallenges 11 k) :=
  execution_hvzk _ _ (witness_valid k) (blinding k) _ _ _
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (k : ℕ) (nu : PMF F) (eta inner : PMF Fˣ) :
    honestExecution (claim k) (witness k) nu eta inner =
      (H.honestInteraction (claim k) (witness k) nu).bind
        (compressionKernel (claim k) (independentChallenges eta inner k)) :=
  honest_execution_eq_postprocessing _ _ _ _ _
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : H.ResultValid (claim 1) (extractCompressed (claim 1) (fork 1)) :=
  compressed_extraction_soundness _ _ (all_forks_valid 1)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : H.ResultValid relClaim (extractCompressed relClaim outerFork) :=
  compressed_extraction_soundness _ _ (by decide +kernel)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : H.ResultValid innerClaim (extractCompressed innerClaim innerFork) :=
  compressed_extraction_soundness _ _ (by decide +kernel)

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [
    decide (Function.Injective (fun i => (units i : F)^2)),
    decide (compressedVerify (claim 0) (wire 0 0)),
    decide (compressedVerify (claim 1) (wire 1 0)),
    decide (compressedVerify (claim 2) (wire 2 2)),
    decide (checkedExtract (claim 0) (fork 0) = some (.witness (witness 0))),
    decide ((wire 2 0).product = dot_product (masks 2).1 (masks 2).2.1),
    decide ((group_payload (wire 2 0).proof).length = 4),
    decide ((scalar_payload (wire 2 0).proof).length = 2),
    decide (leaf_count ((fork 2).nodes 0).tree₀ = 16),
    decide (((compress (claim 2) (full 2 1) (1,![units 0,units 1])).proof).rounds 1 =
      ((compress (claim 2) (full 2 1) (1,![units 0,units 2])).proof).rounds 1),
    decide (((compress (claim 2) (full 2 1) (1,![units 0,units 1])).proof).rounds 0 =
      ((compress (claim 2) (full 2 1) (1,![units 2,units 3])).proof).rounds 0),
    decide (ValidCompressedFork relClaim outerFork),
    decide (checkedExtract relClaim outerFork = some (.relation outerRelation)),
    decide (∀ i, isRelation (nodeResult relClaim outerFork i) = false),
    decide (outerRelation ≠ 0 ∧ H.Range.relation_eval relClaim.generators outerRelation = 0),
    decide (ValidCompressedFork innerClaim innerFork),
    decide (checkedExtract innerClaim innerFork = some (.relation innerRelation)),
    decide (isRelation (nodeResult innerClaim innerFork 0) = true),
    decide (innerRelation ≠ 0 ∧ H.Range.relation_eval innerClaim.generators innerRelation = 0),
    decide (checkedExtract (claim 1) badOuter = none),
    decide (checkedExtract (claim 1) badEta = none),
    decide (checkedExtract (claim 1) badT = none),
    decide (checkedExtract (claim 1) badZ = none),
    decide (checkedExtract (claim 1) badAnn = none),
    decide (checkedExtract (claim 1) badTree = none),
    decide (¬ compressedVerify (claim 1) { wire 1 1 with product := 0 }),
    decide (¬ compressedVerify { claim 1 with P := 0 } (wire 1 1)),
    decide (¬ compressedVerify { claim 1 with V := 0 } (wire 1 1)),
    decide (compressedVerify { claim 1 with P := 0, V := 0 } (wire 1 0)),
    decide (checkedExtract (claim 1) (fork 1) = some (.witness (witness 1))),
    decide (checkedExtract (claim 2) (fork 2) = some (.witness (witness 2)))]
  for i in List.range checks.length do
    unless checks[i]! do throw (IO.userError s!"compression case {i}")
  for e in List.range 11 do
    unless decide (compressedVerify (claim 2)
      (seededCompressedSimulator (claim 2) e (masks 2) (calls 2))) do
      throw (IO.userError "seeded simulator")
  IO.println "HIDDEN_COMPRESSION_OK 42"

end HiddenCompressionRegression

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := HiddenCompressionRegression.main

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarInnerProductProtocolContract
namespace HiddenScalarRegression
open CryptoHiddenScalarInnerProductProtocolContract CryptoBulletproofsInnerProduct
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
abbrev F := ZMod 5

def gens (k : ℕ) : Range.Generators 5 F k := ⟨1, 2, 3, fun _ => 1, fun _ => 1⟩
def witness (k : ℕ) : Witness 5 k := ⟨fun _ => 1, fun _ => 2, 1⟩
def claim (k : ℕ) : Claim 5 F k :=
  ⟨gens k, multiscalar_mul (witness k).a (gens k).G + multiscalar_mul (witness k).b (gens k).H,
   dot_product (witness k).a (witness k).b • (gens k).B + (witness k).rho • (gens k).Hblind⟩
def masks (k : ℕ) : MaskRandomness 5 k := (fun _ => 1, fun _ => 2, 3, 4)
def challenges : Fin 3 → F := ![0,1,2]
def fork (k : ℕ) := honestFork (claim k) (witness k) (masks k) challenges

theorem valid_witness (k : ℕ) : WitnessValid (claim k) (witness k) := ⟨rfl,rfl⟩
example : ValidFork (claim 0) (fork 0) := by decide +kernel
example : checkedExtract (claim 0) (fork 0) = some (.witness (witness 0)) := by decide +kernel
example : checkedExtract (claim 1) (fork 1) = some (.witness (witness 1)) := by decide +kernel
example : checkedExtract (claim 2) (fork 2) = some (.witness (witness 2)) := by decide +kernel
example (k : ℕ) (e : F) : Verify (claim k) (honestTranscript (claim k) (witness k) (masks k) e) :=
  honest_completeness _ _ (valid_witness k) _ _
example : (fork 0 0).response.left = (masks 0).1 := by decide +kernel
example : (fork 0 0).response.right = (masks 0).2.1 := by decide +kernel
example : (fork 0 0).response.blind = 3 := by decide +kernel
example : (fork 0 1).response.blind = 3 := by decide +kernel
example : (fork 0 2).response.blind = 0 := by decide +kernel
example : (candidate (fork 0)).rho = 1 := by decide +kernel

theorem blinding (k : ℕ) : Function.Bijective (fun x : F => x • (claim k).generators.Hblind) :=
  CryptoPedersenHomomorphicSum.nonzero_generator_bijective
    (CryptoPedersenHomomorphicSum.scalarSetup 2 (by decide)) (by change (2 : F) ≠ 0; decide)
example (k : ℕ) (e : F) : realView (claim k) (witness k) e = seededSimView (claim k) e :=
  real_view_eq_seeded_sim_view _ _ (valid_witness k) (blinding k) e
example (k : ℕ) (nu : PMF F) : honestInteraction (claim k) (witness k) nu =
    simulatedInteraction (claim k) nu := interaction_hvzk _ _ (valid_witness k) (blinding k) nu
example (e : F) (r : MaskRandomness 5 1) : Verify (claim 1) (seededSimulator (claim 1) e r) :=
  simulator_accepts _ _ _

-- Same P,V and announcement, nonaffine third response: explicit G-H relation.
def relClaim : Claim 5 F 0 := ⟨⟨1,1,1,fun _ => 1,fun _ => 1⟩,0,0⟩
def relFork : Fin 3 → Transcript 5 F 0 :=
  ![⟨⟨0,0,0⟩,0,⟨0,0,0⟩⟩, ⟨⟨0,0,0⟩,1,⟨0,0,0⟩⟩,
    ⟨⟨0,0,0⟩,2,⟨fun _ => 1,fun _ => 4,1⟩⟩]
def rel : Range.RelationCoefficients 5 0 := ⟨fun _ => 1,fun _ => 4,0,0,0⟩
example : ValidFork relClaim relFork := by decide +kernel
example : checkedExtract relClaim relFork = some (.relation rel) := by decide +kernel
example : rel ≠ 0 := by decide +kernel
example : Range.relation_eval relClaim.generators rel = 0 := by decide +kernel
example : ResultValid relClaim (extract relFork) := three_point_extraction_soundness _ _ (by decide +kernel)

def repeated := fun i : Fin 3 => fork 0 (if i = 2 then 1 else i)
def badAnn := fun i : Fin 3 => if i = 2 then
  { fork 0 i with announcement := { (fork 0 i).announcement with slope := 0 } } else fork 0 i
def badResponse := fun i : Fin 3 => if i = 2 then
  { fork 0 i with response := { (fork 0 i).response with blind := 1 } } else fork 0 i
example : checkedExtract (claim 0) repeated = none := by decide +kernel
example : checkedExtract (claim 0) badAnn = none := by decide +kernel
example : checkedExtract (claim 0) badResponse = none := by decide +kernel
example : checkedExtract { claim 0 with P := 0 } (fork 0) = none := by decide +kernel
example : checkedExtract { claim 0 with V := 0 } (fork 0) = none := by decide +kernel

-- Two evaluations do not fix an arbitrary quadratic polynomial's coefficients.
-- The perturbation changes coefficient data, not a fixed public statement.
def perturb (e : F) : F := e * (e - 1)
example : perturb 0 = 0 ∧ perturb 1 = 0 ∧ perturb 2 ≠ 0 := by decide +kernel
example : Interp.interpolate_quad challenges (fun e => perturb (challenges e)) 2 = 1 := by decide +kernel

-- J=0: SAME public claim, two valid witnesses, distinguishable joint transcripts.
def degenerate : Claim 5 F 0 := ⟨⟨1,0,1,fun _ => 1,fun _ => 1⟩,3,2⟩
def wa : Witness 5 0 := ⟨fun _ => 1,fun _ => 2,0⟩
def wb : Witness 5 0 := ⟨fun _ => 2,fun _ => 1,0⟩
def leakMask : MaskRandomness 5 0 := (fun _ => 1,fun _ => 0,0,0)
def leak := honestTranscript degenerate wa leakMask 0
example : WitnessValid degenerate wa ∧ WitnessValid degenerate wb := by decide +kernel
example : Verify degenerate leak := by decide +kernel

theorem no_second_mask : ¬ ∃ r, honestTranscript degenerate wb r 0 = leak := by
  rintro ⟨r,h⟩
  have hl : r.1 0 = 1 := by
    simpa [honestTranscript, respond, leak, leakMask] using
      congrArg (fun tr : Transcript 5 F 0 => tr.response.left 0) h
  have hr : r.2.1 0 = 0 := by
    simpa [honestTranscript, respond, leak, leakMask] using
      congrArg (fun tr : Transcript 5 F 0 => tr.response.right 0) h
  have ht := congrArg (fun tr : Transcript 5 F 0 => tr.announcement.slope) h
  have hbad : (1 : F) = 2 := by
    simpa [honestTranscript, commit, cross, dot_product, Fin.sum_univ_succ,
      degenerate, wb, wa, leak, leakMask, hl, hr] using ht
  exact (by decide : (1 : F) ≠ 2) hbad

theorem degenerate_views_differ : realView degenerate wa 0 ≠ realView degenerate wb 0 := by
  intro h
  have hs : leak ∈ (realView degenerate wa 0).support := (real_support _ _ _ _).mpr ⟨leakMask,rfl⟩
  rw [h] at hs
  exact no_second_mask ((real_support _ _ _ _).mp hs)
example : ¬ Function.Bijective (fun x : F => x • degenerate.generators.Hblind) := by decide +kernel
example : ¬ Function.Surjective (fun x : F => x • ((1,0) : F × F)) := by decide +kernel
example : ((1,0) : F × F) ≠ 0 := by decide +kernel

-- Runtime checks are separate from kernel proofs and PMF equalities.
def main : IO Unit := do
  let checks : List (String × Bool) := [
    ("honest0", decide (checkedExtract (claim 0) (fork 0) = some (.witness (witness 0)))),
    ("honest1", decide (checkedExtract (claim 1) (fork 1) = some (.witness (witness 1)))),
    ("honest2", decide (checkedExtract (claim 2) (fork 2) = some (.witness (witness 2)))),
    ("relation", decide (checkedExtract relClaim relFork = some (.relation rel))),
    ("repeated", decide (checkedExtract (claim 0) repeated = none)),
    ("bad-announcement", decide (checkedExtract (claim 0) badAnn = none)),
    ("bad-response", decide (checkedExtract (claim 0) badResponse = none)),
    ("wrong-P", decide (checkedExtract { claim 0 with P := 0 } (fork 0) = none)),
    ("wrong-V", decide (checkedExtract { claim 0 with V := 0 } (fork 0) = none)),
    ("nonzero-relation", decide (rel ≠ 0)),
    ("zero-evaluation", decide (Range.relation_eval relClaim.generators rel = 0)),
    ("two-point-residual", decide (perturb 0 = 0 ∧ perturb 1 = 0 ∧ perturb 2 ≠ 0)),
    ("same-claim-witnesses", decide (WitnessValid degenerate wa ∧ WitnessValid degenerate wb)),
    ("non-surjective", decide (¬ Function.Surjective (fun x : F => x • ((1,0) : F × F))))]
  for (name, ok) in checks do
    unless ok do throw (IO.userError name)
  for e in List.range 5 do
    unless decide (Verify (claim 1) (seededSimulator (claim 1) (e : F) (masks 1))) do
      throw (IO.userError "simulator")
  IO.println "HIDDEN_SCALAR_OK 19"
end HiddenScalarRegression

def main : IO Unit := HiddenScalarRegression.main

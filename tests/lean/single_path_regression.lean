import Verification.CryptoHiddenScalarSinglePathContract
namespace SinglePathRegression
open CryptoHiddenScalarSinglePathContract CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
set_option maxRecDepth 50000
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
abbrev Z := ZMod 5

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def unitCall (i : Fin 2) : Zˣ := Units.mk0 (i.val+1)
  ((by decide +kernel : ∀ i : Fin 2, (i.val+1 : Z) ≠ 0) i)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerLaw : CallLaw (Snapshot 5 Nat) Z Z id where
  size := 3
  size_pos := by decide
  call := fun _ i => if i.val < 2 then 0 else 1
  beta := 2/3
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaLaw : CallLaw (Snapshot 5 Nat) Zˣ Zˣ id where
  size := 2
  size_pos := by decide
  call := fun _ => unitCall
  beta := 1/2
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def roundLaw : CallLaw (Snapshot 5 Nat) Zˣ Z (fun x => (x : Z)^2) where
  size := 2
  size_pos := by decide
  call := fun s i => unitCall (if s.memory % 2 = 0 then i else 1-i)
  beta := 1/2
  beta_nonneg := by norm_num
  mass := by
    intro s
    by_cases h : s.memory % 2 = 0
    · simp only [h, if_true]; exact (by decide +kernel)
    · simp only [h, if_false]; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def tree : (k : ℕ) → TreePlan 5 Nat k
  | 0 => .leaf
  | k+1 => .node roundLaw 0 (tree k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def plan (k : ℕ) : ProtocolPlan 5 Nat k := ⟨outerLaw,0,⟨etaLaw,0,tree k⟩⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ann : F.Announcement Z := ⟨0,0,0⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def claim (k : ℕ) : F.Claim 5 Z k := ⟨⟨1,1,1,fun _ => 1,fun _ => 1⟩,0,0⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
/-- Tape determines failures, never resampled within a path. -/
def model (k mode : ℕ) : AdversaryModel 5 Z Nat Nat := ⟨mode,0,fun tape s req =>
  match req with
  | .commit => if tape=1 then none else some
      ((if tape=5 then .scalar 0 0 else .announcement ann),s.memory+1,1)
  | .outer e => if tape=2 ∨ (tape=11 ∧ e=1) then none else some
      ((if tape=6 then .announcement ann else .scalar 0 (if tape=9 then 1 else 0)),s.memory+1,1)
  | .binding _ => if tape=3 then none else some
      ((if tape=7 then .scalar 0 0 else if k=0 then .leaf (if tape=10 then 1 else 0) (if tape=10
        then 1 else 0)
      else .round ⟨0,0⟩),s.memory+1,1)
  | .inner d _ => if tape=4 then none else some
      ((if tape=8 then .scalar 0 0 else if d=0 then .leaf (if tape=10 then 1 else 0) (if tape=10
        then 1 else 0)
      else .round ⟨0,0⟩),s.memory+1,1)⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def innerSeed : (k : ℕ) → PathSeed (tree k)
  | 0 => ()
  | k+1 => (⟨0,by decide⟩,innerSeed k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def seed (k : ℕ) : SinglePathSeed (plan k) :=
  (⟨0, by change 0 < 3; decide⟩, ⟨0, by change 0 < 2; decide⟩, innerSeed k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def run (k mode : ℕ) := execute (plan k) (claim k) (model k mode) (seed k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def accepts (k mode : ℕ) := (run k mode).any (fun r => r.accepted)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : accepts 0 0 = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : accepts 1 0 = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : accepts 2 0 = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0 0).isSome = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 1).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 2).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 3).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 4).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 5).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 6).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 7).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 8).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0 7).isNone = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0 9).isSome = true ∧ accepts 0 9 = false := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0 10).isSome = true ∧ accepts 0 10 = false := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : accepts 1 10 = false := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ w : SinglePathSeed (plan 0),
    AcceptedRun (plan 0) (claim 0) (model 0 0) w := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan 0) (claim 0) (model 0 0) = 1 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan 0) (claim 0) (model 0 11) = 2/3 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan 1) (claim 1) (model 1 11) = 2/3 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : continuationRate (plan 1) (claim 1) (model 1 11) (afterESplit (plan 1)) ⟨0,by decide⟩ = 1
  := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : continuationRate (plan 1) (claim 1) (model 1 11) (afterESplit (plan 1)) ⟨2,by decide⟩ = 0
  := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Heavy.heavyFraction Finset.univ
    (continuationRate (plan 1) (claim 1) (model 1 11) (afterESplit (plan 1))) (1/2) = 2/3
      := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (max 0 (((2/3 : ℚ)-1/2)/(1-1/2))) = 1/3 := by norm_num
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan 1) (claim 1) (model 1 11) =
    Heavy.average Finset.univ (continuationRate (plan 1) (claim 1) (model 1 11) (afterESplit (plan
      1))) :=
  acceptance_eq_prefix_average _ _ _ _
abbrev cut0 : TreeCut (tree 1) := .here _
abbrev cut1 : TreeCut (tree 1) := .next roundLaw 0 (tree 0) (.here _)
local instance : Fintype cut0.Prefix := TreeCut.instFintypePrefix cut0
local instance : Fintype cut0.Suffix := TreeCut.instFintypeSuffix cut0
local instance : DecidableEq cut0.Suffix := TreeCut.instDecidableEqSuffix cut0
local instance : Fintype cut1.Prefix := TreeCut.instFintypePrefix cut1
local instance : Fintype cut1.Suffix := TreeCut.instFintypeSuffix cut1
local instance : DecidableEq cut1.Suffix := TreeCut.instDecidableEqSuffix cut1
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan 1) (claim 1) (model 1 11) =
    Heavy.average (Finset.univ : Finset ((Fin 3 × Fin 2) × cut0.Prefix))
      (continuationRate (X := (Fin 3 × Fin 2) × cut0.Prefix) (Y := cut0.Suffix)
        (plan 1) (claim 1) (model 1 11) (afterRoundSplit (plan 1) cut0)) :=
  acceptance_eq_prefix_average _ _ _ _
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan 1) (claim 1) (model 1 11) =
    Heavy.average (Finset.univ : Finset ((Fin 3 × Fin 2) × cut1.Prefix))
      (continuationRate (X := (Fin 3 × Fin 2) × cut1.Prefix) (Y := cut1.Suffix)
        (plan 1) (claim 1) (model 1 11) (afterRoundSplit (plan 1) cut1)) :=
  acceptance_eq_prefix_average _ _ _ _
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ tr, ProducedTranscript (plan 0) (claim 0) (model 0 0) (seed 0) tr ∧
    SinglePathProvenance (model 0 0) tr ∧ Comp.compressedVerify (claim 0) tr := by
  obtain ⟨tr,hp,hv⟩ := (accepted_iff_verifies (plan 0) (claim 0) (model 0 0) (seed 0)).mp
    (by decide +kernel)
  exact ⟨tr,hp,produced_provenance _ _ _ _ _ hp,hv⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ ∃ tr, ProducedTranscript (plan 0) (claim 0) (model 0 9) (seed 0) tr ∧
    Comp.compressedVerify (claim 0) tr := by
  rw [← accepted_iff_verifies]; decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ AcceptedRun (plan 1) (claim 1) (model 1 4) (seed 1) :=
  none_not_accepted _ _ _ _ (by rfl)
-- Budget zero does not suppress a single path: no acquisition retry is run.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (plan 1).budget = 0 ∧ accepts 1 0 = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (afterRoundSplit (plan 1) cut1).symm ((afterRoundSplit (plan 1) cut1) (seed 1)) = seed 1
  :=
  Equiv.symm_apply_apply _ _
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1 0).map (fun r => (r.transcript.rounds 0 : Z)) = some 2 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : max 0 ((acceptanceRate (plan 1) (claim 1) (model 1 11) - (1/2))/(1-1/2)) ≤
    Heavy.heavyFraction Finset.univ (continuationRate (plan 1) (claim 1) (model 1 11)
      (afterESplit (plan 1))) (1/2) := by
  have : Nonempty (Fin (plan 1).law.size) := ⟨⟨0,by decide⟩⟩
  exact heavy_prefix_lower _ _ _ _ _ (by norm_num)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ y tr, ProducedTranscript (plan 1) (claim 1) (model 1 11)
    ((afterESplit (plan 1)).symm (⟨0,by decide⟩,y)) tr ∧
    SinglePathProvenance (model 1 11) tr ∧ Comp.compressedVerify (claim 1) tr :=
  heavy_prefix_has_execution (plan 1) (claim 1) (model 1 11) (afterESplit (plan 1))
    (⟨0,by decide⟩ : Fin 3) (1/2) (by norm_num) (by decide +kernel)
end SinglePathRegression
open SinglePathRegression

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [accepts 0 0, accepts 1 0, accepts 2 0,
    (run 1 1).isNone,(run 1 2).isNone,(run 1 3).isNone,(run 1 4).isNone,
    (run 1 5).isNone,(run 1 6).isNone,(run 1 7).isNone,(run 1 8).isNone,
    (run 0 7).isNone,(run 0 9).isSome && !accepts 0 9,
    (run 0 10).isSome && !accepts 0 10,!accepts 1 10,
    decide (CryptoHiddenScalarSinglePathContract.acceptanceRate (plan 1) (claim 1) (model 1 11) =
      2/3)]
  if checks.all id then IO.println s!"SINGLE_PATH_OK {checks.length}"
  else throw (IO.userError "single-path regression failed")

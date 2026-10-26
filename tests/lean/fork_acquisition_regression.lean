import Verification.CryptoHiddenScalarForkAcquisitionContract
namespace ForkAcquisitionRegression
open CryptoHiddenScalarForkAcquisitionContract CryptoBulletproofsTreeExtraction
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
set_option maxRecDepth 40000
abbrev Z := ZMod 11

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def unit (n : Z) (h : n ≠ 0) : Zˣ := Units.mk0 n h
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def u2 : Zˣ := unit 2 (by decide)
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def u3 : Zˣ := unit 3 (by decide)
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def u4 : Zˣ := unit 4 (by decide)
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def units : List Zˣ := [1,u2,u3,u4]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ann : F.Announcement Z := ⟨0,0,0⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def claim (k : ℕ) : F.Claim 11 Z k := ⟨⟨1,2,3,fun _ => 1,fun _ => 1⟩,0,0⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def model (k : ℕ) : AdversaryModel 11 Z Unit Nat :=
  ⟨(), 0, fun _ s req => some ((match req with
    | .commit => .announcement ann
    | .outer _ => .scalar 0 0
    | .binding _ => if k = 0 then .leaf 0 0 else .round ⟨0,0⟩
    | .inner d _ => if d = 0 then .leaf 0 0 else .round ⟨0,0⟩),s.memory+1,1)⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ipaSchedule : (k : ℕ) → IPASchedule 11 k
  | 0 => ()
  | k+1 => units.map (fun x => (x, ipaSchedule k))
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etas (k : ℕ) : EtaSchedule 11 k := [(1,ipaSchedule k),(u2,ipaSchedule k)]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def schedule (k : ℕ) : ProbeSchedule 11 k := [ (0,etas k), (1,etas k), (2,etas k) ]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def run (k : ℕ) := acquireCompressedFork (claim k) (model k) (schedule k)
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ok (r : AcquisitionRun 11 Z k) := r.outcome.isOk

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def abort : AdversaryModel 11 Z Unit Nat := ⟨(),0,fun _ _ _ => none⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrong : AdversaryModel 11 Z Unit Nat := ⟨(),0,fun _ _ _ => some (.leaf 0 0,0,0)⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badOuter : AdversaryModel 11 Z Unit Nat :=
  { model 0 with step := fun t s r => match r with
    | .outer _ => some (.scalar 1 0, s.memory, 0)
    | _ => (model 0).step t s r }
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def badLeaf : AdversaryModel 11 Z Unit Nat :=
  { model 1 with step := fun t s r => match r with
    | .inner _ _ => some (.leaf 1 0,s.memory,1)
    | _ => (model 1).step t s r }
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def negOne : Zˣ := unit (-1) (by decide)
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def collide : IPASchedule 11 1 := [(1,()),(negOne,()),(u2,()),(u3,())]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def deficient : EtaSchedule 11 1 := [(1,collide),(u2,collide)]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
/-- First tree exhausts; the SAME eta is retried with fresh child probes. -/
def retryEtas : EtaSchedule 11 1 := [(1,[]),(1,ipaSchedule 1),(u2,ipaSchedule 1)]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def retrySchedule : ProbeSchedule 11 1 := [(0,retryEtas),(1,etas 1),(2,etas 1)]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
/-- Failed e branch is retried, rather than permanently forbidden. -/
def retryOuter : ProbeSchedule 11 1 := [(0,[]),(0,etas 1),(1,etas 1),(2,etas 1)]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def duplicateOuter : ProbeSchedule 11 0 := [(0,etas 0),(0,etas 0),(1,etas 0),(2,etas 0)]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def duplicateEta : EtaSchedule 11 0 := [(1,()),(1,()),(u2,())]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def duplicates : ProbeSchedule 11 0 := [(0,duplicateEta),(1,etas 0),(2,etas 0)]
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def early : ProbeSchedule 11 0 := schedule 0 ++ [(3,[]),(4,[])]

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def extractValid (k : ℕ) : Bool := match (run k).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed (claim k) f with
    | .witness w => decide (w = ⟨fun _ => 0, fun _ => 0, 0⟩)
    | .relation _ => false

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).trace.oracleQueries = 10 := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).trace.stateRestores = 9 := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ok (run 0) = true := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ok (acquireCompressedFork (claim 0) abort []) = false := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (acquireCompressedFork (claim 0) abort []).trace.oracleQueries = 1 := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (acquireCompressedFork (claim 0) abort []).trace.stateRestores = 0 := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (acquireCompressedFork (claim 0) (model 0) []).trace.subtreeFailures = 1
  := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : idealQueries 0 = 10 := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : idealQueries 1 = 34 := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : idealQueries 2 = 130 := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : idealQueries 3 = 514 := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (initialSnapshot (model 0)).tapePos = 0 := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (advance (initialSnapshot (model 0)) (.outer 2) 3 4).tapePos = 4 := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (advance (initialSnapshot (model 0)) (.outer 2) 3 4).history = [.outer 2] := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (restore (model 0) ⟨initialSnapshot (model 0), .initial⟩).memory = 0 := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (scan 1 id id (fun n : Nat => ⟨some n,[.query]⟩) [2,3] []).1 = [2] := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (scan 1 id id (fun n : Nat => ⟨some n,[.query]⟩) [2,3] []).2 = [.restore,.query] := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (collect 2 id id (fun n : Nat => ⟨some n,[.query]⟩) [2,2,3]).value.isSome = true
  := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (collect 2 id id (fun n : Nat => ⟨some n,[.query]⟩) [2,2]).trace =
  [.restore,.query,.restore,.rejected .duplicate,.exhausted] := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (scan 1 Prod.fst id (fun p : Nat × Bool =>
  if p.2 then ⟨some p.1,[.query]⟩ else ⟨none,[.query,.exhausted]⟩)
  [(7,false),(7,true)] []).1 = [7] := rfl
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).trace.length ≤ scheduleFuel (schedule 0) := acquisition_trace_bound _ _ _
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (f : C.CompressedFork 11 Z 1) (h : (run 1).outcome = .ok f) :
  C.ValidCompressedFork (claim 1) f := acquire_valid_compressed_fork _ _ _ f h
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (f : C.CompressedFork 11 Z 1) (h : (run 1).outcome = .ok f) :
  ForkProvenance (model 1) f := acquire_provenance_sound _ _ _ f h
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (f : C.CompressedFork 11 Z 1) (h : (run 1).outcome = .ok f) :
  F.ResultValid (claim 1) (C.extractCompressed (claim 1) f) := acquire_and_extract_soundness _ _ _
    f h

namespace Full
export CryptoHiddenScalarInnerProductProtocolContract (Witness honestTranscript)
end Full

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def honestWitness : Full.Witness 11 0 := ⟨fun _ => 1,fun _ => 2,3⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def honestClaim : F.Claim 11 Z 0 := ⟨⟨1,2,3,fun _ => 1,fun _ => 1⟩,3,8⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def honestFull (e : Z) := Full.honestTranscript honestClaim honestWitness
  (fun _ => 4,fun _ => 5,6,7) e

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def honestModel : AdversaryModel 11 Z Unit Nat := ⟨(),0,fun _ s req =>
  match req with
  | .commit => some (.announcement (honestFull 0).announcement,0,1)
  | .outer e => some (.scalar
      (CryptoBulletproofsInnerProduct.dot_product (honestFull e).response.left
        (honestFull e).response.right) (honestFull e).response.blind,e.val,1)
  | .binding _ => some (.leaf ((honestFull s.memory).response.left 0)
      ((honestFull s.memory).response.right 0),s.memory,1)
  | .inner _ _ => none⟩

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroGeneratorsClaim : F.Claim 11 Z 0 := ⟨⟨0,0,0,fun _ => 0,fun _ => 0⟩,0,0⟩
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def innerRelationModel : AdversaryModel 11 Z Unit Nat :=
  { model 0 with step := fun t s req => match req with
    | .binding eta => some (.leaf (eta : Z) 0,s.memory,1)
    | _ => (model 0).step t s req }
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerRelationModel : AdversaryModel 11 Z Unit Nat :=
  { model 0 with step := fun t s req => match req with
    | .outer e => some (.scalar 0 0,e.val,1)
    | .binding _ => some (.leaf (if s.memory = 2 then 1 else 0) 0,s.memory,1)
    | _ => (model 0).step t s req }
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def yieldsRelation (m : AdversaryModel 11 Z Unit Nat) : Bool :=
  match (acquireCompressedFork zeroGeneratorsClaim m (schedule 0)).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed zeroGeneratorsClaim f with
    | .witness _ => false
    | .relation d => decide (d ≠ 0) && decide
        (CryptoBulletproofsRangeWitnessExtraction.relation_eval zeroGeneratorsClaim.generators d =
          0)
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def honestExtract : Bool :=
  match (acquireCompressedFork honestClaim honestModel (schedule 0)).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed honestClaim f with
    | .relation _ => false
    | .witness w => decide (w = honestWitness)

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def finiteSchedule (b : Bool) : ProbeSchedule 11 0 := if b then schedule 0 else []
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Prob.probability (Finset.univ : Finset Bool)
    (Finset.univ.filter fun b => (acquireCompressedFork (claim 0) (model 0)
      (finiteSchedule b)).outcome.isOk) = 1/2 := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (model 0).step () ⟨0,[],4⟩ (.outer 1) ≠
    (model 0).step () ⟨0,[],9⟩ (.outer 1) := by
  intro h
  simp [model] at h
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).trace.oracleQueries ≤ scheduleFuel (schedule 0) := (resource_bounds _ _ _).1
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).trace.stateRestores ≤ scheduleFuel (schedule 0) := (resource_bounds _ _ _).2.1
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).trace.candidateRejections ≤ scheduleFuel (schedule 0) := (resource_bounds _ _
  _).2.2.1
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).trace.subtreeFailures ≤ scheduleFuel (schedule 0) := (resource_bounds _ _ _).2.2.2

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def densityBounds : List ℚ := 1 :: (1/2) :: List.replicate 46 1
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem finite_density : Prob.ConditionalBounds (Finset.univ : Finset Bool)
    (traceTests (claim 0) (model 0) finiteSchedule 48) densityBounds := by decide +kernel
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : densityBounds.prod ≤ Prob.probability (Finset.univ : Finset Bool)
    (Finset.univ.filter fun b => (acquireCompressedFork (claim 0) (model 0)
      (finiteSchedule b)).outcome.isOk) :=
  clean_schedule_probability_lower _ _ _ (by simp) finiteSchedule 48
    (by intro b _; cases b <;> decide +kernel) densityBounds finite_density
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (ht : Clean (run 1).trace) : (run 1).trace.oracleQueries = 34 ∧
    (run 1).trace.stateRestores = 33 := (clean_acquisition_exact _ _ _ ht).2
set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Prob.probability (Finset.univ : Finset Bool)
    (Finset.univ.filter fun b => (acquireCompressedFork (claim 0) (model 0)
      (finiteSchedule b)).outcome.isOk) > 0 := by decide +kernel

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def checks : List Bool := [
  ok (run 0), ok (run 1), ok (run 2),
  (run 1).trace.oracleQueries == 34, (run 2).trace.oracleQueries == 130,
  (run 1).trace.stateRestores == 33, (run 2).trace.stateRestores == 129,
  (run 2).trace.candidateRejections == 0, (run 2).trace.subtreeFailures == 0,
  extractValid 0, extractValid 1, extractValid 2,
  !(ok (acquireCompressedFork (claim 0) wrong (schedule 0))),
  !(ok (acquireCompressedFork (claim 0) badOuter (schedule 0))),
  !(ok (acquireCompressedFork (claim 1) badLeaf (schedule 1))),
  !(ok (acquireCompressedFork (claim 1) (model 1) [(0,deficient),(1,deficient),(2,deficient)])),
  ok (acquireCompressedFork (claim 1) (model 1) retrySchedule),
  (acquireCompressedFork (claim 1) (model 1) retrySchedule).trace.subtreeFailures == 1,
  ok (acquireCompressedFork (claim 1) (model 1) retryOuter),
  (acquireCompressedFork (claim 1) (model 1) retryOuter).trace.subtreeFailures == 1,
  ok (acquireCompressedFork (claim 0) (model 0) duplicateOuter),
  (acquireCompressedFork (claim 0) (model 0) duplicateOuter).trace.oracleQueries == 10,
  (acquireCompressedFork (claim 0) (model 0) duplicateOuter).trace.stateRestores == 10,
  ok (acquireCompressedFork (claim 0) (model 0) duplicates),
  (acquireCompressedFork (claim 0) (model 0) duplicates).trace.candidateRejections == 1,
  ok (acquireCompressedFork (claim 0) (model 0) early),
  (acquireCompressedFork (claim 0) (model 0) early).trace.oracleQueries == 10,
  (acquireCompressedFork (claim 0) (model 0) early).trace == (run 0).trace,
  (acquireCompressedFork (claim 0) abort (schedule 0)).trace.oracleQueries == 1,
  (acquireCompressedFork (claim 0) abort (schedule 0)).trace.stateRestores == 0,
  honestExtract, yieldsRelation innerRelationModel, yieldsRelation outerRelationModel,
  (run 0).trace.length ≤ scheduleFuel (schedule 0),
  (run 1).trace.length ≤ scheduleFuel (schedule 1),
  (run 2).trace.length ≤ scheduleFuel (schedule 2)]
end ForkAcquisitionRegression

set_option maxHeartbeats 12000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let cs := ForkAcquisitionRegression.checks
  unless cs.all id do throw (IO.userError s!"fork acquisition failures: {cs}")
  IO.println s!"FORK_ACQUISITION_OK {cs.length}"

import Verification.CryptoHiddenScalarTapeAverageContract
namespace TapeAverageRegression
open CryptoHiddenScalarTapeAverageContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarSinglePathContract CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
set_option maxRecDepth 50000
local instance : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
abbrev Z := ZMod 5

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def W : TapeLaw Bool where
  weight := fun b => if b then 1/3 else 2/3
  nonneg := by intro b; cases b <;> norm_num
  total := by decide +kernel
-- Different fiber sizes: uniform sampling on the union would change the tape law.
abbrev TinySeed (b : Bool) := Fin (if b then 3 else 1)
instance (b : Bool) : Fintype (TinySeed b) := inferInstanceAs (Fintype (Fin _))
instance (b : Bool) : DecidableEq (TinySeed b) := inferInstanceAs (DecidableEq (Fin _))
instance (b : Bool) : Nonempty (TinySeed b) := ⟨⟨0,by cases b <;> decide⟩⟩
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : W.jointMass TinySeed ⟨false,0⟩ = 2/3 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : W.jointMass TinySeed ⟨true,0⟩ = 1/9 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∑ v : Sigma TinySeed, W.jointMass TinySeed v = 1 := W.jointMass_total TinySeed
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : W.jointRate TinySeed (fun b _ => b) = 1/3 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : eventRate (fun v : Sigma TinySeed => v.1) = 3/4 := by decide +kernel
-- Two microseeds decode to the accepting value: their multiplicity is retained.
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : W.jointRate TinySeed (fun b i => b && decide (i.val < 2)) = 2/9 := by decide +kernel

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaCalls (i : Fin 4) : Zˣ := Units.mk0 (i.val+1)
  ((by decide +kernel : ∀ i : Fin 4, (i.val+1 : Z) ≠ 0) i)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaLaw : CallLaw (Snapshot 5 Nat) Zˣ Zˣ id where
  size := 4
  size_pos := by decide +kernel
  call := fun _ => etaCalls
  beta := 1/4
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerLaw : CallLaw (Snapshot 5 Nat) Z Z id where
  size := 5
  size_pos := by decide +kernel
  call := fun _ i => i.val
  beta := 1/5
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaPlan : EtaPlan 5 Nat 0 := ⟨etaLaw,2,.leaf⟩
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def plan (b : Bool) : ProtocolPlan 5 Nat 0 := ⟨outerLaw,if b then 3 else 4,etaPlan⟩
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def thresholds : ThresholdProfile where
  value := fun i => if i=0 then 1 else if i=1 then 99/100 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by
    intro i
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
    split_ifs <;> norm_num

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ann : F.Announcement Z := ⟨0,0,0⟩
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def claim : F.Claim 5 Z 0 := ⟨⟨1,1,1,fun _ => 0,fun _ => 0⟩,0,0⟩
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def experiment : TapeExperiment 5 Z Bool Nat 0 where
  initial := 0
  step := fun tape s req => if tape then some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 0
    | .binding _ => .leaf 0 0 | .inner _ _ => .leaf 0 0),s.memory+1,1) else none
  plan := plan
  thresholds := fun _ => thresholds

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def B : ℚ := protocolThresholdBound (plan true) thresholds
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (plan true).budget ≠ (plan false).budget := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Fintype.card (experiment.Seed true) = 512000 := by
  norm_num [TapeExperiment.Seed,experiment,plan,ProtocolPlan.Seed,etaPlan,EtaPlan.Seed,
    TreePlan.Seed,outerLaw,etaLaw]
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Fintype.card (experiment.Seed false) = 40960000 := by
  norm_num [TapeExperiment.Seed,experiment,plan,ProtocolPlan.Seed,etaPlan,EtaPlan.Seed,
    TreePlan.Seed,outerLaw,etaLaw]
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : etaThresholdBound etaPlan thresholds.tail = 3577/5000 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : B = 14536674033/125000000000 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < protocolThresholdBound (plan false) thresholds := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan true) claim (experiment.model true) = 1 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : acceptanceRate (plan false) claim (experiment.model false) = 0 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : experiment.guardedBound claim false = 0 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : experiment.guardedBound claim true = B := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem average_value : experiment.averagedBound W claim = B/3 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem average_positive : 0 < experiment.averagedBound W claim := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : experiment.averagedBound W claim ≤ experiment.successProbability W claim :=
  experiment.averaged_acquisition_lower W claim
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ b, ∃ v : experiment.Seed b, 0 < W.jointMass experiment.Seed ⟨b,v⟩ ∧ ∃ f,
    (acquireCompressedFork claim (experiment.model b) ((experiment.plan b).decode
      (experiment.model b) v)).outcome = .ok f ∧ ForkProvenance (experiment.model b) f ∧
      F.ResultValid claim (C.extractCompressed claim f) :=
  experiment.positive_mass_extracts W claim average_positive

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaSeed : etaPlan.Seed := fun i =>
  (⟨i.val, by
    have h := i.isLt
    change i.val < 4
    change i.val < 2 at h
    omega⟩, ())
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def seed (b : Bool) : (plan b).Seed := fun i =>
  (⟨i.val, by
    have h := i.isLt
    change i.val < 5
    change i.val < (if b then 3 else 4) at h
    cases b <;> simp_all <;> omega⟩, etaSeed)
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def run (b : Bool) := acquireCompressedFork claim (experiment.model b)
  ((plan b).decode (experiment.model b) (seed b))
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run true).outcome.isOk = true := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run false).outcome = .error .initialAdversaryAbort := rfl
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run false).trace.oracleQueries = 1 ∧ (run false).trace.stateRestores = 0
  := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < W.jointMass experiment.Seed ⟨true,seed true⟩ :=
  (W.jointMass_pos_iff experiment.Seed _).mpr (by decide +kernel)

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def extractedZero : Bool := match (run true).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed claim f with
    | .relation _ => false
    | .witness w => decide (w = (⟨fun _ => 0,fun _ => 0,0⟩ :
      CryptoHiddenScalarInnerProductProtocolContract.Witness 5 0))
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extractedZero = true := by decide +kernel

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroWeight : TapeLaw Bool where
  weight := fun b => if b then 0 else 1
  nonneg := by intro b; cases b <;> decide
  total := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : experiment.averagedBound zeroWeight claim = 0 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : experiment.averagedBound zeroWeight claim = 0 ∧ (run true).outcome.isOk = true
  := by decide +kernel

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def flat : ThresholdProfile where
  value := fun _ => 1/2
  pos := by intro; norm_num
  le_one := by intro; norm_num
  child_lt := by intro; norm_num
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def flatExperiment := { experiment with thresholds := fun _ => flat }
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : flatExperiment.averagedBound W claim = 0 := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run true).outcome.isOk = true ∧ flatExperiment.averagedBound W claim = 0
  := by decide +kernel
-- Insufficient budgets cannot be repaired by tape averaging.
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def shortExperiment := { experiment with plan := fun _ => ⟨outerLaw,2,etaPlan⟩ }
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : shortExperiment.averagedBound W claim = 0 := by decide +kernel
-- A failed scalar check keeps a full rejected path but its tape contribution is zero.
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def scalarExperiment : TapeExperiment 5 Z Bool Nat 0 := { experiment with
  step := fun _ s req => some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 1
    | .binding _ => .leaf 0 0 | .inner _ _ => .leaf 0 0), s.memory + 1, 1) }
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : scalarExperiment.averagedBound W claim = 0 := by decide +kernel

-- Weighted positivity is exactly about positive-weight positive-bound tapes.
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < W.expectation (fun b => if b then (1/2 : ℚ) else 0) := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬(0 < zeroWeight.expectation (fun b => if b then (1/2 : ℚ) else 0)) := by decide +kernel

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def checks : List Bool := [
  decide (W.jointMass TinySeed ⟨false,0⟩ = 2/3),
  decide (W.jointMass TinySeed ⟨true,0⟩ = 1/9),
  decide (W.jointRate TinySeed (fun b _ => b) = 1/3),
  decide (eventRate (fun v : Sigma TinySeed => v.1) = 3/4),
  decide (W.jointRate TinySeed (fun b i => b && decide (i.val < 2)) = 2/9),
  decide (0 < B),decide (experiment.averagedBound W claim = B/3),
  decide (experiment.guardedBound claim false = 0),
  decide (0 < protocolThresholdBound (plan false) thresholds),
  (run true).outcome.isOk,!(run false).outcome.isOk,
  decide ((run false).trace.oracleQueries = 1),decide ((run false).trace.stateRestores = 0),
  extractedZero,decide (experiment.averagedBound zeroWeight claim = 0),
  decide (flatExperiment.averagedBound W claim = 0),
  decide (shortExperiment.averagedBound W claim = 0),
  decide (scalarExperiment.averagedBound W claim = 0)]
end TapeAverageRegression

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let cs := TapeAverageRegression.checks
  unless cs.all id do throw (IO.userError s!"tape average failures: {cs}")
  IO.println s!"TAPE_AVERAGE_OK {cs.length}"

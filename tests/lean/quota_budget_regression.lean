import Verification.CryptoHiddenScalarQuotaBudgetContract
namespace QuotaBudgetRegression
open CryptoHiddenScalarTapeAverageContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarSinglePathContract CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarHeavyTapeContract CryptoHiddenScalarQuotaMarginContract
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
def extractedZero : Bool := match (run true).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed claim f with
    | .relation _ => false
    | .witness w => decide (w = (⟨fun _ => 0,fun _ => 0,0⟩ :
      CryptoHiddenScalarInnerProductProtocolContract.Witness 5 0))
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
def lowerRoot : ThresholdProfile where
  value := fun i => if i=0 then 999/1000 else if i=1 then 99/100 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by
    intro i
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
    split_ifs <;> norm_num
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def good : TapeExperiment 5 Z Bool Nat 0 := { experiment with
  step := fun _ => experiment.step true
  plan := fun _ => plan true
  thresholds := fun _ => lowerRoot }
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def bGood : ℚ := protocolThresholdBound (plan true) lowerRoot
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem bGood_pos : 0 < bGood := by decide +kernel
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem good_acceptance : W.expectation
  (CryptoHiddenScalarHeavyTapeContract.TapeExperiment.acceptance good claim) = 1
  := by decide +kernel


set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def heterogeneous := { good with plan := plan }

set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def onlyTrue : TapeLaw Bool where
  weight := fun w => if w then 1 else 0
  nonneg := by intro w; cases w <;> norm_num
  total := by decide +kernel
-- An exact zero margin at eta: H=(5/8-1/2)/(1-1/2)=1/4=beta.
set_option maxHeartbeats 800000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def boundary : ThresholdProfile where
  value := fun i => if i=0 then 5/8 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by intro i; simp; norm_num
end QuotaBudgetRegression

namespace BudgetPositiveDepth
open CryptoHiddenScalarQuotaMarginContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarForkRecursiveQuotaContract CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarTapeAverageContract
set_option maxRecDepth 50000
local instance : Fact (Nat.Prime 37) := ⟨by decide +kernel⟩
abbrev Z := ZMod 37
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls (i : Fin 36) : Zˣ := Units.mk0 (i.val+1)
  ((by decide +kernel : ∀ i : Fin 36, (i.val+1 : Z) ≠ 0) i)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def roundLaw : CallLaw (Snapshot 37 Nat) Zˣ Z (fun x => (x:Z)^2) where
  size := 36
  size_pos := by decide
  call := fun _ => calls
  beta := 1/18
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaLaw : CallLaw (Snapshot 37 Nat) Zˣ Zˣ id where
  size := 36
  size_pos := by decide
  call := fun _ => calls
  beta := 1/36
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerLaw : CallLaw (Snapshot 37 Nat) Z Z id where
  size := 37
  size_pos := by decide
  call := fun _ i => i.val
  beta := 1/37
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def tree : TreePlan 37 Nat 1 := .node roundLaw 4 .leaf
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def eta : EtaPlan 37 Nat 1 := ⟨etaLaw,2,tree⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def plan : ProtocolPlan 37 Nat 1 := ⟨outerLaw,3,eta⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def thresholds : ThresholdProfile where
  value := fun i => if i=0 then 999999/1000000 else if i=1 then 9999/10000 else if i=2 then 99/100
    else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by
    intro i
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]
    split_ifs <;> norm_num
end BudgetPositiveDepth


namespace BudgetChecks
open CryptoHiddenScalarQuotaDeficitContract CryptoHiddenScalarQuotaProductContract
open CryptoHiddenScalarQuotaMarginContract CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkRecursiveQuotaContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarHeavyTapeContract CryptoHiddenScalarTapeAverageContract
open CryptoHiddenScalarForkAcquisitionContract QuotaBudgetRegression
set_option maxRecDepth 50000
local instance : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def heterogeneousProfile (i : ℕ) : ℚ := if i = 0 then 1/4 else if i = 1 then 3/4 else 1/2
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def doublePlan := { plan true with budget := 6 }
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def doubleExperiment := { good with plan := fun _ => doublePlan }
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def doubleSeed : doublePlan.Seed := fun i => (⟨i.val % 5, Nat.mod_lt _ (by decide)⟩,etaSeed)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def doubleRun := acquireCompressedFork claim (doubleExperiment.model true)
  (doublePlan.decode (doubleExperiment.model true) doubleSeed)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def doubleExtractedZero : Bool := match doubleRun.outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed claim f with
    | .relation _ => false
    | .witness w => decide (w = (⟨fun _ => 0,fun _ => 0,0⟩ :
      CryptoHiddenScalarInnerProductProtocolContract.Witness 5 0))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def depthOneDouble := { BudgetPositiveDepth.plan with budget := 6 }

open CryptoHiddenScalarQuotaBudgetContract

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def Aroot : ℚ := finiteProductLower doubleExperiment {true}
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def target : ℚ := (1 - Aroot)^2

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem selected_two : chooseBlockCount Aroot target = some 2 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1 - protocolThresholdBound doublePlan lowerRoot ≤ target :=
  selected_root_deficit_le doubleExperiment {true} target 2 selected_two true
    (by simp) (by decide)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1-target)*TapeLaw.mass W {true} ≤ doubleExperiment.averagedBound W claim :=
  selected_average_lower doubleExperiment W claim {true} target 2 selected_two
    (by decide +kernel) (by intro w _; exact (by decide : 6 ≤ 6))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1-doubleExperiment.successProbability W claim ≤
    1-TapeLaw.mass W {true}+TapeLaw.mass W {true}*target :=
  selected_failure_upper doubleExperiment W claim {true} target 2 selected_two
    (by decide +kernel) (by intro w _; exact (by decide : 6 ≤ 6))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1-eventRate (doubleExperiment.success claim true) ≤ target :=
  selected_tape_failure_le doubleExperiment claim {true} target 2 selected_two
    (by decide +kernel) true (by simp) (by decide)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ w, ∃ v : doubleExperiment.Seed w, 0 < W.jointMass doubleExperiment.Seed ⟨w,v⟩ ∧ ∃ f,
    (acquireCompressedFork claim (doubleExperiment.model w)
      ((doubleExperiment.plan w).decode (doubleExperiment.model w) v)).outcome = .ok f ∧
    ForkProvenance (doubleExperiment.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f)
      :=
  selected_extracts doubleExperiment W claim {true} target 2 selected_two
    (by decide +kernel) (by intro w _; exact (by decide : 6 ≤ 6))
    (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1/2) 8 0 ≤ 2/5 :=
  selected_quota_deficit_le 2 8 0 4 _ (2/5) (by intro i _; norm_num) (by decide)
    (by decide +kernel) (by decide)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => -3) 0 2 ≤ 0 :=
  absorbed_quota_deficit_le 2 0 2 _ 0 (by decide) (by norm_num)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1-protocolThresholdBound depthOneDouble BudgetPositiveDepth.thresholds ≤
    (1-protocolProductLower depthOneDouble BudgetPositiveDepth.thresholds)^2 := by
  have h := protocol_block_lower depthOneDouble BudgetPositiveDepth.thresholds 2 (by decide)
  dsimp [blockLower] at h
  linarith
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (protocolProductLower depthOneDouble BudgetPositiveDepth.thresholds)
    ((1-protocolProductLower depthOneDouble BudgetPositiveDepth.thresholds)^2) = some 2 :=
  by decide +kernel
-- A nonempty strict subset of qualifying keeps the excluded positive tape mass.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ({true} : Finset Bool) ⊂ TapeExperiment.qualifying doubleExperiment claim
  := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : TapeLaw.mass W (TapeExperiment.qualifying doubleExperiment claim) = 1 ∧
    TapeLaw.mass W {true} = 1/3 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1-target)*TapeLaw.mass onlyTrue {false} ≤ doubleExperiment.averagedBound onlyTrue claim
  :=
  selected_average_lower doubleExperiment onlyTrue claim {false} target 2
    (by decide +kernel) (by decide +kernel) (by intro w _; exact (by decide : 6 ≤ 6))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1-(1:ℚ))*TapeLaw.mass W ∅ ≤ doubleExperiment.averagedBound W claim :=
  selected_average_lower doubleExperiment W claim ∅ 1 0
    (by decide +kernel) (by simp) (by simp)

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (0) (0) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (0) (1/2) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (0) (1) = some 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (0) (2) = some 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1) (0) = some 1 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1) (1/2) = some 1 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1) (1) = some 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1) (2) = some 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/2) (0) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/2) (1) = some 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/2) (3/2) = some 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (-1/2) (1) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (3/2) (1) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/2) (-1) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1) (-1) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/2) (1/8) = some 3 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/4) (2/5) = some 4 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/10) (1/2) = some 7 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (3/4) (1/64) = some 3 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : geometricBudgetCap (1/4) (2/5) = 6 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1-(1/2:ℚ))^3 = 1/8 ∧ (1/8:ℚ) < (1-1/2)^2 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 1 (fun _ => 1/2) 2 0 = 1/4 ∧ (1/8:ℚ) < 1/4 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (1/4) (2/5) = some 4 ∧ quotaDeficit 2 (fun _ => 1/2) 4 0 = 5/16 ∧
  (5/16:ℚ) ≤ 2/5 ∧ (2/5:ℚ) < quotaDeficit 2 (fun _ => 1/2) 3 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 3 (fun _ => 1/2) 0 3 = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount Aroot target = some 2 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : protocolMarginCertificate doublePlan lowerRoot := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : protocolMarginCertificate depthOneDouble BudgetPositiveDepth.thresholds
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ (3*2 ≤ (plan true).budget) := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1-protocolThresholdBound (plan true) lowerRoot) > target := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : finiteProductLower doubleExperiment ∅ = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (finiteProductLower doubleExperiment ∅) (1/2) = none := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (finiteProductLower doubleExperiment ∅) 1 = some 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < finiteProductLower doubleExperiment {false} ∧ TapeLaw.mass onlyTrue {false} = 0
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1-target)*TapeLaw.mass onlyTrue {false} = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : TapeLaw.mass W {true} = 1/3 ∧ 0 < (1-target)*TapeLaw.mass W {true} := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : doubleRun.outcome.isOk = true := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : doubleExtractedZero = true := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run false).trace.oracleQueries = 1 ∧ (run false).trace.stateRestores = 0
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : chooseBlockCount (protocolProductLower depthOneDouble BudgetPositiveDepth.thresholds)
  ((1-protocolProductLower depthOneDouble BudgetPositiveDepth.thresholds)^2) = some 2
  := by decide +kernel

end BudgetChecks
open BudgetChecks QuotaBudgetRegression
open CryptoHiddenScalarQuotaBudgetContract CryptoHiddenScalarQuotaDeficitContract
open CryptoHiddenScalarQuotaProductContract CryptoHiddenScalarQuotaMarginContract
open CryptoHiddenScalarThresholdQuotaContract CryptoHiddenScalarHeavyTapeContract

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let cs : List Bool := [
    decide (chooseBlockCount (0) (0) = none),
    decide (chooseBlockCount (0) (1/2) = none),
    decide (chooseBlockCount (0) (1) = some 0),
    decide (chooseBlockCount (0) (2) = some 0),
    decide (chooseBlockCount (1) (0) = some 1),
    decide (chooseBlockCount (1) (1/2) = some 1),
    decide (chooseBlockCount (1) (1) = some 0),
    decide (chooseBlockCount (1) (2) = some 0),
    decide (chooseBlockCount (1/2) (0) = none),
    decide (chooseBlockCount (1/2) (1) = some 0),
    decide (chooseBlockCount (1/2) (3/2) = some 0),
    decide (chooseBlockCount (-1/2) (1) = none),
    decide (chooseBlockCount (3/2) (1) = none),
    decide (chooseBlockCount (1/2) (-1) = none),
    decide (chooseBlockCount (1) (-1) = none),
    decide (chooseBlockCount (1/2) (1/8) = some 3),
    decide (chooseBlockCount (1/4) (2/5) = some 4),
    decide (chooseBlockCount (1/10) (1/2) = some 7),
    decide (chooseBlockCount (3/4) (1/64) = some 3),
    decide (geometricBudgetCap (1/4) (2/5) = 6),
    decide ((1-(1/2:ℚ))^3 = 1/8 ∧ (1/8:ℚ) < (1-1/2)^2),
    decide (quotaDeficit 1 (fun _ => 1/2) 2 0 = 1/4 ∧ (1/8:ℚ) < 1/4),
    decide (chooseBlockCount (1/4) (2/5) = some 4 ∧ quotaDeficit 2 (fun _ => 1/2) 4 0 = 5/16 ∧
      (5/16:ℚ) ≤ 2/5 ∧ (2/5:ℚ) < quotaDeficit 2 (fun _ => 1/2) 3 0),
    decide (quotaDeficit 3 (fun _ => 1/2) 0 3 = 0),
    decide (chooseBlockCount Aroot target = some 2),
    decide (protocolMarginCertificate doublePlan lowerRoot),
    decide (protocolMarginCertificate depthOneDouble BudgetPositiveDepth.thresholds),
    decide (¬ (3*2 ≤ (plan true).budget)),
    decide ((1-protocolThresholdBound (plan true) lowerRoot) > target),
    decide (finiteProductLower doubleExperiment ∅ = 0),
    decide (chooseBlockCount (finiteProductLower doubleExperiment ∅) (1/2) = none),
    decide (chooseBlockCount (finiteProductLower doubleExperiment ∅) 1 = some 0),
    decide (0 < finiteProductLower doubleExperiment {false} ∧ TapeLaw.mass onlyTrue {false} = 0),
    decide ((1-target)*TapeLaw.mass onlyTrue {false} = 0),
    decide (TapeLaw.mass W {true} = 1/3 ∧ 0 < (1-target)*TapeLaw.mass W {true}),
    decide (doubleRun.outcome.isOk = true),
    decide (doubleExtractedZero = true),
    decide ((run false).trace.oracleQueries = 1 ∧ (run false).trace.stateRestores = 0),
    decide (chooseBlockCount (protocolProductLower depthOneDouble BudgetPositiveDepth.thresholds)
      ((1-protocolProductLower depthOneDouble BudgetPositiveDepth.thresholds)^2) = some 2)]
  unless cs.all id do throw (IO.userError s!"quota budget failures: {cs}")
  IO.println s!"QUOTA_BUDGET_OK {cs.length}"

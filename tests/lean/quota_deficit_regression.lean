import Verification.CryptoHiddenScalarQuotaDeficitContract
namespace QuotaDeficitRegression
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
end QuotaDeficitRegression

namespace DeficitPositiveDepth
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
end DeficitPositiveDepth


namespace DeficitChecks
open CryptoHiddenScalarQuotaDeficitContract CryptoHiddenScalarQuotaProductContract
open CryptoHiddenScalarQuotaMarginContract CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkRecursiveQuotaContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarHeavyTapeContract CryptoHiddenScalarTapeAverageContract
open CryptoHiddenScalarForkAcquisitionContract QuotaDeficitRegression
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
def depthOneDouble := { DeficitPositiveDepth.plan with budget := 6 }

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (n T L j : ℕ) (p : ℕ → ℚ) (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) :
    quotaDeficit n p (T+L) j ≤ quotaDeficit n p T j * quotaDeficit n p L j :=
  quota_deficit_submultiplicative n T L j p hp
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (n T j : ℕ) (p : ℕ → ℚ) (hp : ∀ i < n, 0 ≤ p i ∧ p i ≤ 1) (hj : j < n) :
    quotaDeficit n p T j ≤ (1 - ∏ i ∈ Finset.Ico j n, p i) ^ (T/(n-j)) :=
  quota_deficit_product_floor n T j p hp hj
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (p : ℕ → ℚ) (T : ℕ) : quotaDeficit 1 p T 0 = (1-p 0)^T := by
  simp [quotaDeficit, quota_one]
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (a : ℚ) : blockLower a 1 = a := by simp [blockLower]
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (a : ℚ) : blockLower a 0 = 0 := by simp [blockLower]
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 3 heterogeneousProfile 8 0 ≤
    quotaDeficit 3 heterogeneousProfile 4 0 ^ 2 :=
  quota_deficit_block_upper 3 8 4 2 0 _
    (by intro i _; dsimp [heterogeneousProfile]; split_ifs <;> norm_num) (by decide)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1 - quota 4 8 1 (1/8) ≤ (1-(5/8:ℚ)^4)^2 :=
  linear_uniform_deficit_upper 4 8 2 1 (1/8) (5/8) (by decide) (by norm_num)
    (by norm_num) (by decide) (by norm_num) (by norm_num)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (protocolProductLower doublePlan lowerRoot) 2 ≤
    protocolThresholdBound doublePlan lowerRoot := protocol_block_lower _ _ 2 (by decide)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < blockLower (protocolProductLower depthOneDouble DeficitPositiveDepth.thresholds) 2 :=
  block_lower_positive _ _ (protocol_product_positive _ _ (by decide +kernel))
    (protocol_product_range _ _).2 (by decide)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (protocolProductLower depthOneDouble DeficitPositiveDepth.thresholds) 2 ≤
    protocolThresholdBound depthOneDouble DeficitPositiveDepth.thresholds :=
  protocol_block_lower _ _ 2 (by decide)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < blockLower (finiteProductLower doubleExperiment {true}) 2 * TapeLaw.mass W {true} ∧
    blockLower (finiteProductLower doubleExperiment {true}) 2 * TapeLaw.mass W {true} ≤
      doubleExperiment.averagedBound W claim ∧
    doubleExperiment.averagedBound W claim ≤ doubleExperiment.successProbability W claim :=
  certified_block_success_lower doubleExperiment W claim {true} 2 (by decide)
    (by decide +kernel) (by decide +kernel) (by intro w _; exact (by decide : 6 ≤ 6))
    (by intro w _; exact (by decide +kernel : protocolMarginCertificate doublePlan lowerRoot))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ w, ∃ v : doubleExperiment.Seed w, 0 < W.jointMass doubleExperiment.Seed ⟨w,v⟩ ∧ ∃ f,
    (acquireCompressedFork claim (doubleExperiment.model w)
      ((doubleExperiment.plan w).decode (doubleExperiment.model w) v)).outcome = .ok f ∧
    ForkProvenance (doubleExperiment.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f)
      :=
  block_extracts doubleExperiment W claim {true} 2 (by decide)
    (by decide +kernel) (by decide +kernel) (by intro w _; exact (by decide : 6 ≤ 6))
    (by intro w _; exact (by decide +kernel : protocolMarginCertificate doublePlan lowerRoot))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1 - doubleExperiment.successProbability W claim ≤ 1 - TapeLaw.mass W {true} +
    TapeLaw.mass W {true} * (1-finiteProductLower doubleExperiment {true})^2 :=
  block_failure_upper doubleExperiment W claim {true} 2 (by decide +kernel)
    (by intro w _; exact (by decide : 6 ≤ 6))

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 0 (fun _ => -3) 5 0 = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 3 (fun _ => 2) 2 4 = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 3 (fun _ => 1/2) 2 0 = 1 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1/2) 0 0 = 1 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1/2) 5 0 ≤ quotaDeficit 2 (fun _ => 1/2) 0 0 ^ 3
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (1/4) 0 = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower 0 5 = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower 1 5 = 1 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 0) 8 0 = 1 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1) 2 0 = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1/2) 2 0 = 3/4 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1/2) 4 0 = 5/16 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (1/4) 2 = 7/16 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (1/4) 2 < quotaLower 2 (fun _ => 1/2) 4 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1/2) 2 0 > (1-(1/2:ℚ)^2)^2 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 2 (fun _ => 1/2) 2 0 > (1-(1/2:ℚ))^2 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 3 heterogeneousProfile 2 1 = 5/8 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 3 heterogeneousProfile 8 0 < quotaDeficit 3 heterogeneousProfile 4 0 ^ 2
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaDeficit 1 (fun _ => 2/5) 7 0 = (3/5:ℚ)^7 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (linearQuotaProduct 4 1 (1/8)) 1 = linearQuotaProduct 4 1 (1/8)
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (linearQuotaProduct 4 1 (1/8)) 2 = 42735/65536 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quota 4 8 1 (1/8) = 1027845/1048576 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower ((5/8:ℚ)^4) 2 = 4729375/16777216 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : protocolMarginCertificate (plan true) lowerRoot ∧ ¬ (3*2 ≤ (plan true).budget)
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : protocolThresholdBound (plan true) lowerRoot < blockLower (protocolProductLower (plan
  true) lowerRoot) 2 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : protocolMarginCertificate doublePlan lowerRoot := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : protocolProductLower doublePlan lowerRoot = bGood := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < blockLower (protocolProductLower doublePlan lowerRoot) 2 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : protocolMarginCertificate depthOneDouble DeficitPositiveDepth.thresholds
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : finiteProductLower doubleExperiment ∅ = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (finiteProductLower doubleExperiment ∅) 2 * TapeLaw.mass W ∅ = 0
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < finiteProductLower doubleExperiment {false} ∧ TapeLaw.mass onlyTrue {false} = 0
  := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : blockLower (finiteProductLower doubleExperiment {false}) 2 * TapeLaw.mass onlyTrue
  {false} = 0 := by decide +kernel

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

end DeficitChecks
open DeficitChecks QuotaDeficitRegression
open CryptoHiddenScalarQuotaDeficitContract CryptoHiddenScalarQuotaProductContract
open CryptoHiddenScalarForkProgressProbabilityContract CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarThresholdQuotaContract CryptoHiddenScalarQuotaMarginContract
open CryptoHiddenScalarHeavyTapeContract

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let cs : List Bool := [
    decide (quotaDeficit 0 (fun _ => -3) 5 0 = 0),
    decide (quotaDeficit 3 (fun _ => 2) 2 4 = 0),
    decide (quotaDeficit 3 (fun _ => 1/2) 2 0 = 1),
    decide (quotaDeficit 2 (fun _ => 1/2) 0 0 = 1),
    decide (quotaDeficit 2 (fun _ => 1/2) 5 0 ≤ quotaDeficit 2 (fun _ => 1/2) 0 0 ^ 3),
    decide (blockLower (1/4) 0 = 0),
    decide (blockLower 0 5 = 0),
    decide (blockLower 1 5 = 1),
    decide (quotaDeficit 2 (fun _ => 0) 8 0 = 1),
    decide (quotaDeficit 2 (fun _ => 1) 2 0 = 0),
    decide (quotaDeficit 2 (fun _ => 1/2) 2 0 = 3/4),
    decide (quotaDeficit 2 (fun _ => 1/2) 4 0 = 5/16),
    decide (blockLower (1/4) 2 = 7/16),
    decide (blockLower (1/4) 2 < quotaLower 2 (fun _ => 1/2) 4 0),
    decide (quotaDeficit 2 (fun _ => 1/2) 2 0 > (1-(1/2:ℚ)^2)^2),
    decide (quotaDeficit 2 (fun _ => 1/2) 2 0 > (1-(1/2:ℚ))^2),
    decide (quotaDeficit 3 heterogeneousProfile 2 1 = 5/8),
    decide (quotaDeficit 3 heterogeneousProfile 8 0 < quotaDeficit 3 heterogeneousProfile 4 0 ^ 2),
    decide (quotaDeficit 1 (fun _ => 2/5) 7 0 = (3/5:ℚ)^7),
    decide (blockLower (linearQuotaProduct 4 1 (1/8)) 1 = linearQuotaProduct 4 1 (1/8)),
    decide (blockLower (linearQuotaProduct 4 1 (1/8)) 2 = 42735/65536),
    decide (quota 4 8 1 (1/8) = 1027845/1048576),
    decide (blockLower ((5/8:ℚ)^4) 2 = 4729375/16777216),
    decide (protocolMarginCertificate (plan true) lowerRoot ∧ ¬ (3*2 ≤ (plan true).budget)),
    decide (protocolThresholdBound (plan true) lowerRoot < blockLower (protocolProductLower (plan
      true) lowerRoot) 2),
    decide (protocolMarginCertificate doublePlan lowerRoot),
    decide (protocolProductLower doublePlan lowerRoot = bGood),
    decide (0 < blockLower (protocolProductLower doublePlan lowerRoot) 2),
    decide (protocolMarginCertificate depthOneDouble DeficitPositiveDepth.thresholds),
    decide (finiteProductLower doubleExperiment ∅ = 0),
    decide (blockLower (finiteProductLower doubleExperiment ∅) 2 * TapeLaw.mass W ∅ = 0),
    decide (0 < finiteProductLower doubleExperiment {false} ∧ TapeLaw.mass onlyTrue {false} = 0),
    decide (blockLower (finiteProductLower doubleExperiment {false}) 2 * TapeLaw.mass onlyTrue
      {false} = 0),
    decide (doubleRun.outcome.isOk = true),
    decide (doubleExtractedZero = true),
    decide ((run false).trace.oracleQueries = 1 ∧ (run false).trace.stateRestores = 0)]
  unless cs.all id do throw (IO.userError s!"quota deficit failures: {cs}")
  IO.println s!"QUOTA_DEFICIT_OK {cs.length}"

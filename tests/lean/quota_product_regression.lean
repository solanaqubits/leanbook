import Verification.CryptoHiddenScalarQuotaProductContract
namespace QuotaProductRegression
open CryptoHiddenScalarTapeAverageContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarSinglePathContract CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarHeavyTapeContract CryptoHiddenScalarQuotaMarginContract
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
local instance : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
abbrev Z := ZMod 5
def W : TapeLaw Bool where
  weight := fun b => if b then 1/3 else 2/3
  nonneg := by intro b; cases b <;> norm_num
  total := by decide +kernel
-- Different fiber sizes: uniform sampling on the union would change the tape law.
abbrev TinySeed (b : Bool) := Fin (if b then 3 else 1)
instance (b : Bool) : Fintype (TinySeed b) := inferInstanceAs (Fintype (Fin _))
instance (b : Bool) : DecidableEq (TinySeed b) := inferInstanceAs (DecidableEq (Fin _))
instance (b : Bool) : Nonempty (TinySeed b) := ⟨⟨0,by cases b <;> decide⟩⟩
def etaCalls (i : Fin 4) : Zˣ := Units.mk0 (i.val+1)
  ((by decide +kernel : ∀ i : Fin 4, (i.val+1 : Z) ≠ 0) i)
def etaLaw : CallLaw (Snapshot 5 Nat) Zˣ Zˣ id where
  size := 4
  size_pos := by decide +kernel
  call := fun _ => etaCalls
  beta := 1/4
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def outerLaw : CallLaw (Snapshot 5 Nat) Z Z id where
  size := 5
  size_pos := by decide +kernel
  call := fun _ i => i.val
  beta := 1/5
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def etaPlan : EtaPlan 5 Nat 0 := ⟨etaLaw,2,.leaf⟩
def plan (b : Bool) : ProtocolPlan 5 Nat 0 := ⟨outerLaw,if b then 3 else 4,etaPlan⟩
def thresholds : ThresholdProfile where
  value := fun i => if i=0 then 1 else if i=1 then 99/100 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by intro i; simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]; split_ifs <;> norm_num

def ann : F.Announcement Z := ⟨0,0,0⟩
def claim : F.Claim 5 Z 0 := ⟨⟨1,1,1,fun _ => 0,fun _ => 0⟩,0,0⟩
def experiment : TapeExperiment 5 Z Bool Nat 0 where
  initial := 0
  step := fun tape s req => if tape then some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 0
    | .binding _ => .leaf 0 0 | .inner _ _ => .leaf 0 0),s.memory+1,1) else none
  plan := plan
  thresholds := fun _ => thresholds

def B : ℚ := protocolThresholdBound (plan true) thresholds
def etaSeed : etaPlan.Seed := fun i => (⟨i.val,by have h := i.isLt; change i.val < 4; change i.val < 2 at h; omega⟩,())
def seed (b : Bool) : (plan b).Seed := fun i =>
  (⟨i.val,by have h := i.isLt; change i.val < 5; change i.val < (if b then 3 else 4) at h; cases b <;> simp_all <;> omega⟩,etaSeed)
def run (b : Bool) := acquireCompressedFork claim (experiment.model b)
  ((plan b).decode (experiment.model b) (seed b))
def extractedZero : Bool := match (run true).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed claim f with
    | .relation _ => false
    | .witness w => decide (w = (⟨fun _ => 0,fun _ => 0,0⟩ : CryptoHiddenScalarInnerProductProtocolContract.Witness 5 0))
def flat : ThresholdProfile where
  value := fun _ => 1/2
  pos := by intro; norm_num
  le_one := by intro; norm_num
  child_lt := by intro; norm_num
def flatExperiment := { experiment with thresholds := fun _ => flat }

def lowerRoot : ThresholdProfile where
  value := fun i => if i=0 then 999/1000 else if i=1 then 99/100 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by intro i; simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]; split_ifs <;> norm_num
def good : TapeExperiment 5 Z Bool Nat 0 := { experiment with
  step := fun _ => experiment.step true
  plan := fun _ => plan true
  thresholds := fun _ => lowerRoot }
def bGood : ℚ := protocolThresholdBound (plan true) lowerRoot
theorem bGood_pos : 0 < bGood := by decide +kernel
theorem good_acceptance : W.expectation (CryptoHiddenScalarHeavyTapeContract.TapeExperiment.acceptance good claim) = 1 := by decide +kernel
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass W (CryptoHiddenScalarHeavyTapeContract.TapeExperiment.qualifying good claim) = 1 := by decide +kernel

example : treeMarginCertificate (TreePlan.leaf : TreePlan 5 Nat 0) flat := by decide +kernel
example : protocolMarginCertificate (plan true) lowerRoot := by decide +kernel
example : protocolMarginCertificate (plan false) lowerRoot := by decide +kernel
example : 0 < protocolThresholdBound (plan true) lowerRoot :=
  protocol_certificate_positive _ _ (by decide +kernel)
example : finiteRootLower good ∅ = 0 := by decide +kernel
example : finiteRootLower good {true} = bGood := by decide +kernel
example : finiteRootLower good {false,true} = bGood := by decide +kernel
example : finiteRootLower good {true} = 8711401623057/125000000000000 := by decide +kernel
example : 0 < finiteRootLower good {true} :=
  finiteRootLower_positive _ _ (by simp) (by intro w _; exact (by decide +kernel : protocolMarginCertificate (plan true) lowerRoot))

def heterogeneous := { good with plan := plan }
example : finiteRootLower heterogeneous {false,true} = bGood := by decide +kernel
example : protocolThresholdBound (plan true) lowerRoot < protocolThresholdBound (plan false) lowerRoot := by decide +kernel

def onlyTrue : TapeLaw Bool where
  weight := fun w => if w then 1 else 0
  nonneg := by intro w; cases w <;> norm_num
  total := by decide +kernel
example : ({false} : Finset Bool).Nonempty ∧ TapeLaw.mass onlyTrue {false} = 0 := by decide +kernel
example : 0 < finiteRootLower good {false} ∧ finiteRootLower good {false} * TapeLaw.mass onlyTrue {false} = 0 := by decide +kernel
example : ¬ protocolMarginCertificate { plan true with budget := 2 } lowerRoot := by decide +kernel
example : ¬ etaMarginCertificate { etaPlan with budget := 1 } lowerRoot.tail := by decide +kernel
example : ¬ protocolMarginCertificate (plan true) flat := by decide +kernel
-- An exact zero margin at eta: H=(5/8-1/2)/(1-1/2)=1/4=beta.
def boundary : ThresholdProfile where
  value := fun i => if i=0 then 5/8 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by intro i; simp; norm_num
example : thresholdDensity boundary 1 = 1/4 := by decide +kernel
example : ¬ etaMarginCertificate etaPlan boundary := by decide +kernel
example : etaThresholdBound etaPlan boundary = 0 := by decide +kernel
example : protocolMarginCertificate (experiment.plan false) (experiment.thresholds false) ∧
    experiment.guardedBound claim false = 0 := by decide +kernel
example : (run false).trace.oracleQueries = 1 ∧ (run false).trace.stateRestores = 0 := by decide +kernel
example : extractedZero = true := by decide +kernel
example : (run true).outcome.isOk ∧ flatExperiment.averagedBound W claim = 0 := by decide +kernel
example : 0 < finiteRootLower good {true} * TapeLaw.mass W {true} :=
  (certified_success_lower good W claim {true} (by decide +kernel) (by decide +kernel)
    (by intro w _; exact (by decide +kernel : protocolMarginCertificate (plan true) lowerRoot))).1
example : ∃ w, ∃ v : good.Seed w, 0 < W.jointMass good.Seed ⟨w,v⟩ ∧ ∃ f,
    (acquireCompressedFork claim (good.model w) ((good.plan w).decode (good.model w) v)).outcome =
      .ok f ∧ ForkProvenance (good.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
  certified_extracts good W claim {true} (by decide +kernel) (by decide +kernel)
    (by intro w _; exact (by decide +kernel : protocolMarginCertificate (plan true) lowerRoot))
example : ∃ w, ∃ v : good.Seed w, 0 < W.jointMass good.Seed ⟨w,v⟩ ∧ ∃ f,
    (acquireCompressedFork claim (good.model w) ((good.plan w).decode (good.model w) v)).outcome =
      .ok f ∧ ForkProvenance (good.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
  global_certified_extracts good W claim (999/1000) 1 (by norm_num) (by intro; rfl)
    (le_of_eq good_acceptance.symm) (by norm_num)
    (by intro w _; exact (by decide +kernel : protocolMarginCertificate (plan true) lowerRoot))
end QuotaProductRegression

namespace ProductPositiveDepth
open CryptoHiddenScalarQuotaMarginContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarForkRecursiveQuotaContract CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarTapeAverageContract
set_option maxRecDepth 50000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 37) := ⟨by decide +kernel⟩
abbrev Z := ZMod 37
def calls (i : Fin 36) : Zˣ := Units.mk0 (i.val+1)
  ((by decide +kernel : ∀ i : Fin 36, (i.val+1 : Z) ≠ 0) i)
def roundLaw : CallLaw (Snapshot 37 Nat) Zˣ Z (fun x => (x:Z)^2) where
  size := 36
  size_pos := by decide
  call := fun _ => calls
  beta := 1/18
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def etaLaw : CallLaw (Snapshot 37 Nat) Zˣ Zˣ id where
  size := 36
  size_pos := by decide
  call := fun _ => calls
  beta := 1/36
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def outerLaw : CallLaw (Snapshot 37 Nat) Z Z id where
  size := 37
  size_pos := by decide
  call := fun _ i => i.val
  beta := 1/37
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def tree : TreePlan 37 Nat 1 := .node roundLaw 4 .leaf
def eta : EtaPlan 37 Nat 1 := ⟨etaLaw,2,tree⟩
def plan : ProtocolPlan 37 Nat 1 := ⟨outerLaw,3,eta⟩
def thresholds : ThresholdProfile where
  value := fun i => if i=0 then 999999/1000000 else if i=1 then 9999/10000 else if i=2 then 99/100 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by intro i; simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false]; split_ifs <;> norm_num
example : treeMarginCertificate tree thresholds.tail.tail := by decide +kernel
example : etaMarginCertificate eta thresholds.tail := by decide +kernel
example : protocolMarginCertificate plan thresholds := by decide +kernel
example : 0 < protocolThresholdBound plan thresholds := protocol_certificate_positive _ _ (by decide +kernel)
example : ¬ treeMarginCertificate (.node roundLaw 3 .leaf) thresholds.tail.tail := by decide +kernel
example : ¬ treeMarginCertificate tree QuotaProductRegression.flat := by decide +kernel
end ProductPositiveDepth


namespace ProductChecks
open CryptoHiddenScalarQuotaProductContract CryptoHiddenScalarQuotaMarginContract
open CryptoHiddenScalarForkProgressProbabilityContract CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarThresholdQuotaContract CryptoHiddenScalarHeavyTapeContract
open CryptoHiddenScalarForkAcquisitionContract CryptoHiddenScalarTapeAverageContract
open QuotaProductRegression
set_option maxRecDepth 50000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩

example : quotaLower 0 (fun _ => -3) 5 0 = 1 := by decide +kernel
example : quotaLower 3 (fun _ => 2) 2 4 = 1 := by decide +kernel
example : quotaLower 3 (fun _ => 2) 0 0 = 0 := by decide +kernel
example : quotaLower 4 (fun _ => -2) 2 1 = 0  := CryptoHiddenScalarQuotaProductContract.quota_insufficient _ _ _ _ (by decide)
example : quotaLower 3 (fun i => (i:ℚ)+2) 2 1 = 12 := by decide +kernel
example : quotaLower 3 (fun i => (i:ℚ)+2) 2 1 = ∏ i ∈ Finset.Ico (1 : ℕ) 3, ((i:ℚ)+2) :=
  quota_diagonal 3 1 (fun i => (i:ℚ)+2) (by decide)
example : quotaLower 2 (fun _ => 1/2) 2 0 = 1/4 := by decide +kernel
example : quotaLower 2 (fun _ => 1/2) 3 0 = 1/2 := by decide +kernel
example : quotaLower 2 (fun _ => 1) 2 0 = quotaLower 2 (fun _ => 1) 8 0 := by decide +kernel
example : quotaLower 1 (fun _ => 2) 2 0 < quotaLower 1 (fun _ => 2) 1 0 := by decide +kernel
example : linearQuotaProduct 0 (-3) 5 = 1 := by decide +kernel
example : linearQuotaProduct 4 1 (1/8) = 105/256 := by decide +kernel
example : linearQuotaProduct 3 (3/5) (3/10) = 0 := by decide +kernel
example : 0 < (5/8:ℚ)^4 ∧ (5/8:ℚ)^4 ≤ linearQuotaProduct 4 1 (1/8) ∧
    linearQuotaProduct 4 1 (1/8) ≤ quota 4 6 1 (1/8) :=
  uniform_margin_power_lower 4 6 1 (1/8) (5/8) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by norm_num) (by norm_num)
example : 0 < (2:ℚ)^0 ∧ (2:ℚ)^0 ≤ linearQuotaProduct 0 2 0 := by decide +kernel
example : protocolProductLower (plan true) lowerRoot = bGood := by decide +kernel
example : protocolProductLower (plan false) lowerRoot < protocolThresholdBound (plan false) lowerRoot := by decide +kernel
example : protocolProductLower ProductPositiveDepth.plan ProductPositiveDepth.thresholds =
    protocolThresholdBound ProductPositiveDepth.plan ProductPositiveDepth.thresholds := by decide +kernel
example : 0 < protocolProductLower ProductPositiveDepth.plan ProductPositiveDepth.thresholds :=
  protocol_product_positive _ _ (by decide +kernel)

def shortPlan := { plan true with budget := 2 }
def shortExperiment := { good with plan := fun _ => shortPlan }
-- Required counterexample: even the singleton minimum comparison fails without T>=3.
example : 0 < protocolProductLower shortPlan lowerRoot ∧
    protocolThresholdBound shortPlan lowerRoot = 0 := by decide +kernel
example : finiteRootLower shortExperiment {true} < finiteProductLower shortExperiment {true} := by decide +kernel
example : finiteProductLower good ∅ = 0 := by decide +kernel
example : finiteProductLower heterogeneous {false,true} = bGood := by decide +kernel
example : finiteProductLower heterogeneous {false,true} ≤ finiteRootLower heterogeneous {false,true} :=
  finiteProductLower_le_root _ _ (by intro w _; cases w <;> decide +kernel)
example : 0 < finiteProductLower good {false} ∧
    finiteProductLower good {false} * TapeLaw.mass onlyTrue {false} = 0 := by decide +kernel
example : 0 < finiteProductLower good {true} * TapeLaw.mass W {true} ∧
    finiteProductLower good {true} * TapeLaw.mass W {true} ≤ good.averagedBound W claim ∧
    good.averagedBound W claim ≤ good.successProbability W claim :=
  certified_product_success_lower good W claim {true} (by decide +kernel) (by decide +kernel)
    (by intro w _; exact (by decide +kernel : protocolMarginCertificate (plan true) lowerRoot))
example : ∃ w, ∃ v : good.Seed w, 0 < W.jointMass good.Seed ⟨w,v⟩ ∧ ∃ f,
    (acquireCompressedFork claim (good.model w) ((good.plan w).decode (good.model w) v)).outcome =
      .ok f ∧ ForkProvenance (good.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
  product_extracts good W claim {true} (by decide +kernel) (by decide +kernel)
    (by intro w _; exact (by decide +kernel : protocolMarginCertificate (plan true) lowerRoot))
end ProductChecks

open QuotaProductRegression ProductChecks CryptoHiddenScalarQuotaProductContract
open CryptoHiddenScalarForkProgressProbabilityContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarQuotaMarginContract CryptoHiddenScalarHeavyTapeContract

def main : IO Unit := do
  let cs : List Bool := [
    decide (quotaLower 0 (fun _ => -3) 5 0 = 1),
    decide (quotaLower 3 (fun _ => 2) 2 4 = 1),
    decide (quotaLower 4 (fun _ => -2) 2 1 = 0),
    decide (quotaLower 3 (fun i => (i:ℚ)+2) 2 1 = 12),
    decide (quotaLower 2 (fun _ => 1/2) 2 0 = 1/4),
    decide (quotaLower 2 (fun _ => 1/2) 3 0 = 1/2),
    decide (quotaLower 2 (fun _ => 1) 2 0 = quotaLower 2 (fun _ => 1) 8 0),
    decide (quotaLower 1 (fun _ => 2) 2 0 < quotaLower 1 (fun _ => 2) 1 0),
    decide (linearQuotaProduct 0 (-3) 5 = 1),
    decide (linearQuotaProduct 4 1 (1/8) = 105/256),
    decide (linearQuotaProduct 3 (3/5) (3/10) = 0),
    decide ((5/8:ℚ)^4 ≤ linearQuotaProduct 4 1 (1/8)),
    decide (protocolProductLower (plan true) lowerRoot = bGood),
    decide (protocolProductLower (plan false) lowerRoot < protocolThresholdBound (plan false) lowerRoot),
    decide (0 < protocolProductLower ProductPositiveDepth.plan ProductPositiveDepth.thresholds),
    decide (protocolProductLower ProductPositiveDepth.plan ProductPositiveDepth.thresholds = protocolThresholdBound ProductPositiveDepth.plan ProductPositiveDepth.thresholds),
    decide (0 < protocolProductLower shortPlan lowerRoot),
    decide (protocolThresholdBound shortPlan lowerRoot = 0),
    decide (finiteRootLower shortExperiment {true} < finiteProductLower shortExperiment {true}),
    decide (finiteProductLower good ∅ = 0),
    decide (finiteProductLower heterogeneous {false,true} = bGood),
    decide (finiteProductLower heterogeneous {false,true} ≤ finiteRootLower heterogeneous {false,true}),
    decide (0 < finiteProductLower good {false}),
    decide (finiteProductLower good {false} * TapeLaw.mass onlyTrue {false} = 0),
    decide (0 < finiteProductLower good {true} * TapeLaw.mass W {true}),
    (run true).outcome.isOk, extractedZero,
    decide ((run false).trace.oracleQueries = 1 ∧ (run false).trace.stateRestores = 0)]
  unless cs.all id do throw (IO.userError s!"quota product failures: {cs}")
  IO.println s!"QUOTA_PRODUCT_OK {cs.length}"

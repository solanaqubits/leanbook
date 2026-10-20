import Verification.CryptoHiddenScalarHeavyTapeContract
namespace HeavyTapeRegression
open CryptoHiddenScalarTapeAverageContract CryptoHiddenScalarThresholdQuotaContract
open CryptoHiddenScalarSinglePathContract CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoHiddenScalarHeavyTapeContract
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

def w3 : TapeLaw (Fin 3) where
  weight := fun i => if i=0 then 0 else if i=1 then 1/3 else 2/3
  nonneg := by intro i; split_ifs <;> norm_num
  total := by decide +kernel
def a3 (i : Fin 3) : ℚ := if i=2 then 1 else 0
example : w3.expectation a3 = 2/3 := by decide +kernel
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass w3 (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy a3 (fun _ => 1/2)) = 2/3 := by decide +kernel
example : max 0 ((w3.expectation a3-1/2)/(1-1/2)) = 1/3 := by decide +kernel
example : max 0 ((w3.expectation a3-1/2)/(1-1/2)) ≤
    CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass w3 (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy a3 (fun _ => 1/2)) :=
  CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy_mass_lower w3 a3 (1/2) (by norm_num) (by intro i; unfold a3; split_ifs <;> norm_num)
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass w3 {0} = 0 := by decide +kernel
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass w3 ({1,2} \ {2}) = 1/3 := by decide +kernel
example : max 0 (1-1/3 : ℚ) ≤ CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass w3 {2} := by decide +kernel

def half : TapeLaw Bool where
  weight := fun _ => 1/2
  nonneg := by intro; norm_num
  total := by decide +kernel
def varying (w : Bool) : ℚ := if w then 1/10 else 9/10
def rates (w : Bool) : ℚ := if w then 1 else 4/5
example : half.expectation rates = 9/10 := by decide +kernel
example : half.expectation varying = 1/2 := by decide +kernel
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass half (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy rates varying) = 1/2 := by decide +kernel
example : (half.expectation rates-half.expectation varying)/(1-half.expectation varying) = 4/5 := by decide +kernel
example : ¬ ((half.expectation rates-half.expectation varying)/(1-half.expectation varying) ≤
    CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass half (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy rates varying)) := by decide +kernel
example : max 0 (half.expectation rates-half.expectation varying) ≤
    CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass half (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy rates varying) :=
  CryptoHiddenScalarHeavyTapeContract.TapeLaw.variable_mass_lower half rates varying
    (by intro w; cases w <;> norm_num [rates]) (by intro w; cases w <;> norm_num [varying])
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass half (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy (fun _ => 1) (fun _ => 1)) = 1 :=
  CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass_one_of_acceptance_one half _ _ (by intro; norm_num)
    (by intro; norm_num) (CryptoHiddenScalarHeavyTapeContract.TapeLaw.expectation_const half 1)
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass half (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy (fun _ => 99/100) (fun _ => 1)) = 0 := by decide +kernel

-- Original dependent seed law, including repeated accepting decoder images.
example : W.jointMass TinySeed ⟨false,0⟩ = 2/3 := by decide +kernel
example : W.jointMass TinySeed ⟨true,0⟩ = 1/9 := by decide +kernel
example : W.jointRate TinySeed (fun b i => b && decide (i.val < 2)) = 2/9 := by decide +kernel
example : eventRate (fun v : Sigma TinySeed => v.1) = 3/4 := by decide +kernel

-- An actual accepting model with fixed quota plan and root threshold below one.
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
example : bGood ≤ good.successProbability W claim := by
  have h := CryptoHiddenScalarHeavyTapeContract.TapeExperiment.global_success_lower good W claim (999/1000) 1 bGood
    (by norm_num) bGood_pos.le (by intro w; rfl)
    (le_of_eq good_acceptance.symm) (by intro w _; exact le_refl _)
  norm_num at h ⊢; exact h
example : ∃ w, ∃ v : good.Seed w, 0 < W.jointMass good.Seed ⟨w,v⟩ ∧ ∃ f,
    (acquireCompressedFork claim (good.model w) ((good.plan w).decode (good.model w) v)).outcome =
      .ok f ∧ ForkProvenance (good.model w) f ∧ F.ResultValid claim (C.extractCompressed claim f) := by
  exact CryptoHiddenScalarHeavyTapeContract.TapeExperiment.global_acceptance_extracts good W claim (999/1000) 1 bGood
    (by norm_num) bGood_pos (by intro w; exact le_refl _)
    (le_of_eq good_acceptance.symm) (by intro w _; exact le_refl _) (by norm_num)
-- Direct executable witness and failure trace from the same transition model.
example : extractedZero = true := by decide +kernel
example : (run false).trace.oracleQueries = 1 ∧ (run false).trace.stateRestores = 0 := by decide +kernel
example : (run true).outcome.isOk = true := by decide +kernel
example : CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass W (CryptoHiddenScalarHeavyTapeContract.TapeExperiment.qualifying flatExperiment claim) = 1/3 := by decide +kernel
example : flatExperiment.averagedBound W claim = 0 := by decide +kernel
example : (run true).outcome.isOk = true ∧ flatExperiment.averagedBound W claim = 0 := by decide +kernel

def checks : List Bool := [decide (w3.expectation a3 = 2/3),
  decide (CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass w3 {0} = 0),decide (CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass w3 {2} = 2/3),
  decide (half.expectation rates = 9/10),decide (half.expectation varying = 1/2),
  decide (CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass half (CryptoHiddenScalarHeavyTapeContract.TapeLaw.heavy rates varying) = 1/2),
  decide ((half.expectation rates-half.expectation varying)/(1-half.expectation varying) = 4/5),
  decide (W.jointMass TinySeed ⟨true,0⟩ = 1/9),
  decide (W.jointRate TinySeed (fun b i => b && decide (i.val < 2)) = 2/9),
  decide (0 < bGood),decide (W.expectation (CryptoHiddenScalarHeavyTapeContract.TapeExperiment.acceptance good claim) = 1),
  (run true).outcome.isOk,extractedZero,!(run false).outcome.isOk,
  decide (CryptoHiddenScalarHeavyTapeContract.TapeLaw.mass W (CryptoHiddenScalarHeavyTapeContract.TapeExperiment.qualifying flatExperiment claim) = 1/3),
  decide (flatExperiment.averagedBound W claim = 0)]
end HeavyTapeRegression

def main : IO Unit := do
  let cs := HeavyTapeRegression.checks
  unless cs.all id do throw (IO.userError s!"heavy tape failures: {cs}")
  IO.println s!"HEAVY_TAPE_OK {cs.length}"

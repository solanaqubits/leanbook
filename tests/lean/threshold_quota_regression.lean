import Verification.CryptoHiddenScalarThresholdQuotaContract
namespace ThresholdQuotaRegression
open CryptoHiddenScalarThresholdQuotaContract CryptoHiddenScalarSinglePathContract
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkScheduleProgressContract
open CryptoHiddenScalarForkLocalDensityContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
set_option maxRecDepth 50000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
abbrev Z := ZMod 37

def calls8 (i : Fin 8) : Zˣ := Units.mk0 (i.val+1)
  ((by decide +kernel : ∀ i : Fin 8, (i.val+1 : Z) ≠ 0) i)
def calls4 (i : Fin 4) : Zˣ := calls8 ⟨i.val,by omega⟩
def calls32 (i : Fin 32) : Z := i.val

def roundLaw : CallLaw (Snapshot 37 Nat) Zˣ Z (fun x => (x : Z)^2) where
  size := 8
  size_pos := by decide
  call := fun _ => calls8
  beta := 1/8
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def etaLaw : CallLaw (Snapshot 37 Nat) Zˣ Zˣ id where
  size := 4
  size_pos := by decide
  call := fun _ => calls4
  beta := 1/4
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def outerLaw : CallLaw (Snapshot 37 Nat) Z Z id where
  size := 32
  size_pos := by decide
  call := fun _ => calls32
  beta := 1/32
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)

example : Function.Injective (fun i : Fin 8 => (calls8 i : Z)^2) := by decide +kernel
example : ∀ i : Fin 8, Prob.probability Finset.univ
    (Finset.univ.filter fun j : Fin 8 => (calls8 j : Z)^2 = (calls8 i : Z)^2) = 1/8 := by decide +kernel
example : ∀ i : Fin 4, Prob.probability Finset.univ
    (Finset.univ.filter fun j : Fin 4 => calls4 j = calls4 i) = 1/4 := by decide +kernel
example : ∀ i : Fin 32, Prob.probability Finset.univ
    (Finset.univ.filter fun j : Fin 32 => calls32 j = calls32 i) = 1/32 := by decide +kernel

def treePlan : (k : ℕ) → TreePlan 37 Nat k
  | 0 => .leaf
  | k+1 => .node roundLaw 4 (treePlan k)
def etaPlan (k : ℕ) : EtaPlan 37 Nat k := ⟨etaLaw,4,treePlan k⟩
def plan (k : ℕ) : ProtocolPlan 37 Nat k := ⟨outerLaw,3,etaPlan k⟩
def ann : F.Announcement Z := ⟨0,0,0⟩
def claim (k : ℕ) : F.Claim 37 Z k := ⟨⟨1,1,1,fun _ => 0,fun _ => 0⟩,0,0⟩
def model (k : ℕ) : AdversaryModel 37 Z Unit Nat :=
  ⟨(),0,fun _ s req => some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 0
    | .binding _ => if k=0 then .leaf 0 0 else .round ⟨0,0⟩
    | .inner d _ => if d=0 then .leaf 0 0 else .round ⟨0,0⟩),s.memory+1,1)⟩
def st (k : ℕ) := P.toIPA (C.responseClaim (claim k) ann 0 0) 1

def treeSeed : (k : ℕ) → (treePlan k).Seed
  | 0 => ()
  | k+1 => fun i : Fin 4 => (⟨i.val,by change i.val < 8; omega⟩,treeSeed k)
def etaSeed (k : ℕ) : (etaPlan k).Seed := fun i => (⟨i.val,by have h := i.isLt; change i.val < 4; change i.val < 4 at h; omega⟩,treeSeed k)
def seed (k : ℕ) : (plan k).Seed := fun i => (⟨i.val,by have h := i.isLt; change i.val < 32; change i.val < 3 at h; omega⟩,etaSeed k)
def run (k : ℕ) := acquireCompressedFork (claim k) (model k) ((plan k).decode (model k) (seed k))
example : (run 0).outcome.isOk = true := by decide +kernel
example : (run 1).outcome.isOk = true := by decide +kernel
example : (run 2).outcome.isOk = true := by decide +kernel

def thresholds : ThresholdProfile where
  value := fun i => if i=0 then 1 else if i=1 then 999/1000 else if i=2 then 99/100 else 1/2
  pos := by intro i; split_ifs <;> norm_num
  le_one := by intro i; split_ifs <;> norm_num
  child_lt := by intro i; simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false]; split_ifs <;> norm_num

def flat : ThresholdProfile where
  value := fun _ => 1/2
  pos := by intro; norm_num
  le_one := by intro; norm_num
  child_lt := by intro; norm_num

theorem threshold_ipa_value : treeThresholdBound (treePlan 1) thresholds.tail.tail = 74011707/200000000 := by decide +kernel
example : etaThresholdBound (etaPlan 1) thresholds.tail =
    1983204328040277140569872224468428083 / 16000000000000000000000000000000000000 := by decide +kernel
theorem threshold_positive : 0 < protocolThresholdBound (plan 1) thresholds := by decide +kernel
-- Prove acceptance before counting: evaluating the filtered intersection directly
-- creates a quadratic finite-set reduction and can exhaust verification memory.
theorem accepts_each : ∀ w : SinglePathSeed (plan 1), AcceptedRun (plan 1) (claim 1) (model 1) w := by
  decide +kernel

theorem accepts_all : acceptanceRate (plan 1) (claim 1) (model 1) = 1 := by
  simp [acceptanceRate, accepts_each, Prob.probability]
  decide +kernel
example : protocolThresholdBound (plan 1) thresholds ≤ (plan 1).bound (claim 1) (model 1) :=
  acceptance_threshold_le _ _ _ _ (by rw [accepts_all]; exact le_rfl)
example : ∃ w : (plan 1).Seed, ∃ f,
    (acquireCompressedFork (claim 1) (model 1) ((plan 1).decode (model 1) w)).outcome = .ok f ∧
    ForkProvenance (model 1) f ∧ F.ResultValid (claim 1) (C.extractCompressed (claim 1) f) :=
  threshold_positive_extracts _ _ _ _ (by rw [accepts_all]; exact le_rfl) threshold_positive
example : protocolThresholdBound (plan 1) flat = 0 := by decide +kernel
-- Zero threshold bound coexists with success of the unchanged acquirer above.
example : (run 1).outcome.isOk = true ∧ protocolThresholdBound (plan 1) flat = 0 := by decide +kernel
example : quotaLower 3 (fun _ => (1/4 : ℚ)) 4 0 ≤ quotaLower 3 (fun _ => 3/4) 4 0 :=
  quota_profile_mono _ _ _ _ _ (by intros; norm_num) (by intros; norm_num) (by intros; norm_num)
example : quotaLower 3 (fun _ => (7 : ℚ)) 0 3 = 1 := rfl
example : quota 3 2 1 (1/32) = 0 := by decide +kernel
example : quota 4 5 (1/2) (1/8) ≤ quota 4 5 (3/4) (1/8) :=
  quota_density_mono _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Same algebraic context, two reachable snapshots from one fixed adversary tape.
def memClaim : F.Claim 37 Z 0 := ⟨⟨1,1,1,fun _ => 1,fun _ => 1⟩,0,0⟩
def memModel : AdversaryModel 37 Z Unit Nat := ⟨(),0,fun _ s req => match req with
  | .commit => some (.announcement ann,0,1)
  | .outer e => some (.scalar 0 0,if e=0 then 0 else 1,1)
  | .binding _ => some (.leaf (if s.memory=0 then 0 else 1) 0,s.memory,1)
  | .inner _ _ => none⟩
def initObs : Observation memModel (initialSnapshot memModel) .commit := ⟨.announcement ann,0,1,rfl⟩
def e0Obs : Observation memModel initObs.after (.outer 0) := ⟨.scalar 0 0,0,1,rfl⟩
def e1Obs : Observation memModel initObs.after (.outer 1) := ⟨.scalar 0 0,1,1,rfl⟩
def leaf0 : Observation memModel e0Obs.after (.binding 1) := ⟨.leaf 0 0,0,1,rfl⟩
def leaf1 : Observation memModel e1Obs.after (.binding 1) := ⟨.leaf 1 0,1,1,rfl⟩
theorem reachable0 : ReachableSnapshot memModel leaf0.after := leaf0.reachable (e0Obs.reachable (initObs.reachable .initial))
theorem reachable1 : ReachableSnapshot memModel leaf1.after := leaf1.reachable (e1Obs.reachable (initObs.reachable .initial))
def memSt := P.toIPA (C.responseClaim memClaim ann 0 0) 1
example : C.responseClaim memClaim ann 0 0 = C.responseClaim memClaim ann 1 0 := by decide +kernel
example : leaf0.after ≠ leaf1.after := by intro h; have hm := congrArg Snapshot.memory h; norm_num [leaf0,leaf1,Observation.after,advance] at hm
example : (treePlan 0).bound memModel leaf0.after leaf0.packet memSt = 1 := by decide +kernel
example : (treePlan 0).bound memModel leaf1.after leaf1.packet memSt = 0 := by decide +kernel
example : (acquireTree memModel leaf0.after reachable0 leaf0.packet memSt ()).value.isSome = true := by decide +kernel
example : (acquireTree memModel leaf1.after reachable1 leaf1.packet memSt ()).value.isSome = false := by decide +kernel

example : treePathRate (treePlan 0) memModel leaf0.after reachable0 leaf0.packet memSt = 1 := by decide +kernel
example : treePathRate (treePlan 0) memModel leaf1.after reachable1 leaf1.packet memSt = 0 := by decide +kernel
-- A biased seed decoder violates the advertised iid law, while the real collector terminates.
def repeatedSeed : (plan 0).Seed := fun _ => (⟨0,by decide⟩,etaSeed 0)
def repeated := acquireCompressedFork (claim 0) (model 0) ((plan 0).decode (model 0) repeatedSeed)
example : repeated.outcome.toOption = none := by decide +kernel
example : (match repeated.outcome with | .error e => e == .exhaustedE | _ => false) = true := by decide +kernel
theorem trace_nonempty {q k : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] {Ω S : Type}
    (p : F.Claim q A k) (m : AdversaryModel q A Ω S) (schedule : ProbeSchedule q k) :
    (acquireCompressedFork p m schedule).trace ≠ [] := by
  unfold acquireCompressedFork acquireCertified
  split
  · simp
  · split
    · dsimp only; split <;> simp
    · simp
example : repeated.trace ≠ [] := trace_nonempty _ _ _
example : Prob.probability ({()} : Finset Unit) {()} > outerLaw.beta := by decide +kernel
example : 0 < (plan 0).bound (claim 0) (model 0) := by decide +kernel

-- Actual successful fork is passed to the existing algebraic extractor.
def fork := (run 0).outcome.toOption.get (by decide +kernel)
theorem fork_ok : (run 0).outcome = .ok fork := by
  have hok : (run 0).outcome.isOk = true := by decide +kernel
  cases h : (run 0).outcome with
  | error e => simp [h, Except.isOk, Except.toBool] at hok
  | ok f => simp [fork,h,Except.toOption]
example : C.ValidCompressedFork (claim 0) fork := acquire_valid_compressed_fork _ _ _ fork fork_ok
example : F.ResultValid (claim 0) (C.extractCompressed (claim 0) fork) := acquire_and_extract_soundness _ _ _ fork fork_ok

def abortModel : AdversaryModel 37 Z Unit Nat := ⟨(),0,fun _ _ _ => none⟩
def abortRun := acquireCompressedFork (claim 1) abortModel ((plan 1).decode abortModel (seed 1))
example : (plan 1).bound (claim 1) abortModel = 0 := rfl
example : abortRun.outcome = .error .initialAdversaryAbort := rfl
example : abortRun.trace.oracleQueries = 1 := rfl
example : abortRun.trace.stateRestores = 0 := rfl
example : (treePlan 0).bound (model 0) (initialSnapshot (model 0)) (.scalar 0 0) (st 0) = 0 := rfl

def extractedZero : Bool := match (run 0).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed (claim 0) f with
    | .relation _ => false
    | .witness w => decide (w = (⟨fun _ => 0,fun _ => 0,0⟩ : CryptoHiddenScalarInnerProductProtocolContract.Witness 37 0))
example : extractedZero = true := by decide +kernel
example : (run 2).trace.oracleQueries ≤ scheduleFuel ((plan 2).decode (model 2) (seed 2)) :=
  (resource_bounds _ _ _).1
example : ¬(∀ a : Z, Prob.probability Finset.univ
    (Finset.univ.filter fun i : Fin 8 => (calls8 i : Z)^2 = a) ≤ (1/10 : ℚ)) := by decide +kernel


-- Prefix rejection does not destroy a syntactically complete transcript.
def badScalar : AdversaryModel 37 Z Unit Nat :=
  { model 0 with step := fun _ s req => some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 1
    | .binding _ => .leaf 0 0 | .inner _ _ => .leaf 0 0),s.memory+1,1) }
def path0 : SinglePathSeed (plan 0) := (⟨0,by decide⟩,⟨0,by decide⟩,())
def rejected := execute (plan 0) (claim 0) badScalar path0
example : rejected.isSome = true ∧ rejected.any (fun r => r.accepted) = false := by decide +kernel
example : continuationRate (plan 0) (claim 0) badScalar (afterESplit (plan 0)) ⟨0,by decide⟩ = 0 := by decide +kernel
example : acceptanceRate (plan 0) (claim 0) abortModel = 0 := by decide +kernel
example : treePathRate (treePlan 0) (model 0) (initialSnapshot (model 0)) .initial (.scalar 0 0) (st 0) = 0 := by decide +kernel

def badInit : Observation badScalar (initialSnapshot badScalar) .commit := ⟨.announcement ann,1,1,rfl⟩
def badOuter : Observation badScalar badInit.after (.outer 0) := ⟨.scalar 0 1,2,1,rfl⟩
def badEta : Observation badScalar badOuter.after (.binding 1) := ⟨.leaf 0 0,3,1,rfl⟩
example : treePathRate (treePlan 0) badScalar badEta.after
    (badEta.reachable (badOuter.reachable (badInit.reachable .initial))) badEta.packet (st 0) = 1 := by decide +kernel
abbrev zeroCut : TreeCut (treePlan 0) := .here _
local instance : Fintype zeroCut.Prefix := TreeCut.instFintypePrefix zeroCut
local instance : Fintype zeroCut.Suffix := TreeCut.instFintypeSuffix zeroCut
local instance : DecidableEq zeroCut.Suffix := TreeCut.instDecidableEqSuffix zeroCut
example : continuationRate (X := (Fin 32 × Fin 4) × zeroCut.Prefix) (Y := zeroCut.Suffix)
    (plan 0) (claim 0) badScalar
    (afterRoundSplit (plan 0) zeroCut) ((⟨0,by decide⟩,⟨0,by decide⟩),()) = 0 := by decide +kernel

-- Repeated preimages are counted, never replaced by a uniform decoded image.
def duplicateLaw : CallLaw (Snapshot 37 Nat) Z Z id where
  size := 3
  size_pos := by decide
  call := fun _ i => if i.val < 2 then 0 else 1
  beta := 2/3
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
def duplicatePlan : ProtocolPlan 37 Nat 0 := ⟨duplicateLaw,3,etaPlan 0⟩
def onlyZero : AdversaryModel 37 Z Unit Nat :=
  { model 0 with step := fun tape s req => match req with
    | .outer e => if e=0 then (model 0).step tape s req else none
    | _ => (model 0).step tape s req }
example : acceptanceRate duplicatePlan (claim 0) onlyZero = 2/3 := by decide +kernel
example : protocolThresholdBound duplicatePlan flat = 0 := by decide +kernel

def checks : List Bool := [
  decide (0 < protocolThresholdBound (plan 1) thresholds),
  decide (treeThresholdBound (treePlan 1) thresholds.tail.tail = 74011707/200000000),
  decide (acceptanceRate (plan 1) (claim 1) (model 1) = 1),
  (run 0).outcome.isOk,(run 1).outcome.isOk,(run 2).outcome.isOk,
  decide (protocolThresholdBound (plan 1) flat = 0),
  decide (quota 3 2 1 (1/32) = 0),
  decide (treePathRate (treePlan 0) memModel leaf0.after reachable0 leaf0.packet memSt = 1),
  decide (treePathRate (treePlan 0) memModel leaf1.after reachable1 leaf1.packet memSt = 0),
  rejected.isSome, !rejected.any (fun r => r.accepted),
  decide (continuationRate (plan 0) (claim 0) badScalar (afterESplit (plan 0)) ⟨0,by decide⟩ = 0),
  decide (acceptanceRate duplicatePlan (claim 0) onlyZero = 2/3),
  repeated.outcome.isOk == false, !repeated.trace.isEmpty,
  abortRun.trace.oracleQueries == 1, abortRun.trace.stateRestores == 0, extractedZero]
end ThresholdQuotaRegression

def main : IO Unit := do
  let cs := ThresholdQuotaRegression.checks
  unless cs.all id do throw (IO.userError s!"threshold quota failures: {cs}")
  IO.println s!"THRESHOLD_QUOTA_OK {cs.length}"

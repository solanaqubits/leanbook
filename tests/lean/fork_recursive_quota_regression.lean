import Verification.CryptoHiddenScalarForkRecursiveQuotaContract
namespace ForkRecursiveQuotaRegression
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkScheduleProgressContract
open CryptoHiddenScalarForkLocalDensityContract
open CryptoHiddenScalarForkRecursiveQuotaContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
set_option maxRecDepth 50000
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
abbrev Z := ZMod 37

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls8 (i : Fin 8) : Zˣ := Units.mk0 (i.val+1)
  ((by decide +kernel : ∀ i : Fin 8, (i.val+1 : Z) ≠ 0) i)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls4 (i : Fin 4) : Zˣ := calls8 ⟨i.val,by omega⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls32 (i : Fin 32) : Z := i.val

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def roundLaw : CallLaw (Snapshot 37 Nat) Zˣ Z (fun x => (x : Z)^2) where
  size := 8
  size_pos := by decide
  call := fun _ => calls8
  beta := 1/8
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaLaw : CallLaw (Snapshot 37 Nat) Zˣ Zˣ id where
  size := 4
  size_pos := by decide
  call := fun _ => calls4
  beta := 1/4
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerLaw : CallLaw (Snapshot 37 Nat) Z Z id where
  size := 32
  size_pos := by decide
  call := fun _ => calls32
  beta := 1/32
  beta_nonneg := by norm_num
  mass := by intro _; exact (by decide +kernel)

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Function.Injective (fun i : Fin 8 => (calls8 i : Z)^2) := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ i : Fin 8, Prob.probability Finset.univ
    (Finset.univ.filter fun j : Fin 8 => (calls8 j : Z)^2 = (calls8 i : Z)^2) = 1/8
      := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ i : Fin 4, Prob.probability Finset.univ
    (Finset.univ.filter fun j : Fin 4 => calls4 j = calls4 i) = 1/4 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ i : Fin 32, Prob.probability Finset.univ
    (Finset.univ.filter fun j : Fin 32 => calls32 j = calls32 i) = 1/32 := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def treePlan : (k : ℕ) → TreePlan 37 Nat k
  | 0 => .leaf
  | k+1 => .node roundLaw 4 (treePlan k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaPlan (k : ℕ) : EtaPlan 37 Nat k := ⟨etaLaw,2,treePlan k⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def plan (k : ℕ) : ProtocolPlan 37 Nat k := ⟨outerLaw,3,etaPlan k⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ann : F.Announcement Z := ⟨0,0,0⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def claim (k : ℕ) : F.Claim 37 Z k := ⟨⟨1,1,1,fun _ => 0,fun _ => 0⟩,0,0⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def model (k : ℕ) : AdversaryModel 37 Z Unit Nat :=
  ⟨(),0,fun _ s req => some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 0
    | .binding _ => if k=0 then .leaf 0 0 else .round ⟨0,0⟩
    | .inner d _ => if d=0 then .leaf 0 0 else .round ⟨0,0⟩),s.memory+1,1)⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def st (k : ℕ) := P.toIPA (C.responseClaim (claim k) ann 0 0) 1

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem ipa_value : (treePlan 1).bound (model 1) (initialSnapshot (model 1)) (.round ⟨0,0⟩) (st 1)
  = 105/256 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem eta_value : (etaPlan 1).bound (claim 1) (model 1) (initialSnapshot (model 1)) ann 0 0 =
  4305/65536 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem outer_value : (plan 1).bound (claim 1) (model 1) = 2030724465/281474976710656
  := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < (plan 1).bound (claim 1) (model 1) := by rw [outer_value]; norm_num
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (3 : ℚ)*(1/8) < 1 ∧ (1/4 : ℚ) < 105/256 ∧ (2 : ℚ)*(1/32) < 4305/65536 := by norm_num
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (plan 1).bound (claim 1) (model 1) ≤ Prob.probability Finset.univ
    (Finset.univ.filter fun w => (acquireCompressedFork (claim 1) (model 1) ((plan 1).decode (model
      1) w)).outcome.isOk) :=
  (plan 1).probability_lower (claim 1) (model 1)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ w : (plan 1).Seed, ∃ f,
    (acquireCompressedFork (claim 1) (model 1) ((plan 1).decode (model 1) w)).outcome = .ok f ∧
    ForkProvenance (model 1) f ∧ F.ResultValid (claim 1) (C.extractCompressed (claim 1) f) :=
  (plan 1).positive_extracts (claim 1) (model 1) (by rw [outer_value]; norm_num)

-- Explicit distinct seed path; no enumeration of the enormous complete nested seed space.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def treeSeed : (k : ℕ) → (treePlan k).Seed
  | 0 => ()
  | k+1 => fun i : Fin 4 => (⟨i.val,by change i.val < 8; omega⟩,treeSeed k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etaSeed (k : ℕ) : (etaPlan k).Seed := fun i =>
  (⟨i.val, by
    have h := i.isLt
    change i.val < 4
    change i.val < 2 at h
    omega⟩,treeSeed k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def seed (k : ℕ) : (plan k).Seed := fun i =>
  (⟨i.val, by
    have h := i.isLt
    change i.val < 32
    change i.val < 3 at h
    omega⟩,etaSeed k)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def run (k : ℕ) := acquireCompressedFork (claim k) (model k) ((plan k).decode (model k) (seed k))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 0).outcome.isOk = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 1).outcome.isOk = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 2).outcome.isOk = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (plan 0).bound (claim 0) (model 0) = quota 3 3 (3/4) (1/32) := by decide +kernel
-- Increasing depth with these fixed minimal budgets can collapse the conservative bound.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quota 4 4 (105/256) (1/8) < 1/4 := by decide +kernel

-- Actual unchanged collector: 3 accepting calls among 5, independent 3 trials.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def fiveAttempt (i : Fin 5) : Attempt (Fin 5) := ⟨if i.val < 3 then some i else none,[]⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def fiveSpace := Product.productTapes (Finset.univ : Finset (Fin 5)) 3
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def fiveActual : ℚ := Prob.probability fiveSpace
  (fiveSpace.filter fun w => (collect 3 id id fiveAttempt (iidSchedule id w)).value.isSome)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : fiveActual = 6/125 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quota 3 3 (3/5) (3/10) = 0 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∀ a : Fin 5, Prob.probability Finset.univ
    (Finset.univ.filter fun u : Fin 5 => u = a) ≤ (3/10 : ℚ) := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < fiveActual := by decide +kernel

-- Same algebraic context, two reachable snapshots from one fixed adversary tape.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def memClaim : F.Claim 37 Z 0 := ⟨⟨1,1,1,fun _ => 1,fun _ => 1⟩,0,0⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def memModel : AdversaryModel 37 Z Unit Nat := ⟨(),0,fun _ s req => match req with
  | .commit => some (.announcement ann,0,1)
  | .outer e => some (.scalar 0 0,if e=0 then 0 else 1,1)
  | .binding _ => some (.leaf (if s.memory=0 then 0 else 1) 0,s.memory,1)
  | .inner _ _ => none⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def initObs : Observation memModel (initialSnapshot memModel) .commit := ⟨.announcement ann,0,1,rfl⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def e0Obs : Observation memModel initObs.after (.outer 0) := ⟨.scalar 0 0,0,1,rfl⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def e1Obs : Observation memModel initObs.after (.outer 1) := ⟨.scalar 0 0,1,1,rfl⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def leaf0 : Observation memModel e0Obs.after (.binding 1) := ⟨.leaf 0 0,0,1,rfl⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def leaf1 : Observation memModel e1Obs.after (.binding 1) := ⟨.leaf 1 0,1,1,rfl⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem reachable0 : ReachableSnapshot memModel leaf0.after := leaf0.reachable (e0Obs.reachable
  (initObs.reachable .initial))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem reachable1 : ReachableSnapshot memModel leaf1.after := leaf1.reachable (e1Obs.reachable
  (initObs.reachable .initial))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def memSt := P.toIPA (C.responseClaim memClaim ann 0 0) 1
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : C.responseClaim memClaim ann 0 0 = C.responseClaim memClaim ann 1 0 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : leaf0.after ≠ leaf1.after := by
  intro h
  have hm := congrArg Snapshot.memory h
  norm_num [leaf0, leaf1, Observation.after, advance] at hm
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (treePlan 0).bound memModel leaf0.after leaf0.packet memSt = 1 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (treePlan 0).bound memModel leaf1.after leaf1.packet memSt = 0 := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (acquireTree memModel leaf0.after reachable0 leaf0.packet memSt ()).value.isSome = true
  := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (acquireTree memModel leaf1.after reachable1 leaf1.packet memSt ()).value.isSome = false
  := by decide +kernel

-- A biased seed decoder violates the advertised iid law, while the real collector terminates.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def repeatedSeed : (plan 0).Seed := fun _ => (⟨0,by decide⟩,etaSeed 0)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def repeated := acquireCompressedFork (claim 0) (model 0) ((plan 0).decode (model 0) repeatedSeed)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : repeated.outcome.toOption = none := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (match repeated.outcome with | .error e => e == .exhaustedE | _ => false) = true
  := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
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
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : repeated.trace ≠ [] := trace_nonempty _ _ _
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Prob.probability ({()} : Finset Unit) {()} > outerLaw.beta := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 0 < (plan 0).bound (claim 0) (model 0) := by decide +kernel

-- Actual successful fork is passed to the existing algebraic extractor.
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def fork := (run 0).outcome.toOption.get (by decide +kernel)
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem fork_ok : (run 0).outcome = .ok fork := by
  have hok : (run 0).outcome.isOk = true := by decide +kernel
  cases h : (run 0).outcome with
  | error e => simp [h, Except.isOk, Except.toBool] at hok
  | ok f => simp [fork,h,Except.toOption]
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : C.ValidCompressedFork (claim 0) fork := acquire_valid_compressed_fork _ _ _ fork fork_ok
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : F.ResultValid (claim 0) (C.extractCompressed (claim 0) fork)
  := acquire_and_extract_soundness _ _ _ fork fork_ok

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def abortModel : AdversaryModel 37 Z Unit Nat := ⟨(),0,fun _ _ _ => none⟩
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def abortRun := acquireCompressedFork (claim 1) abortModel ((plan 1).decode abortModel (seed 1))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (plan 1).bound (claim 1) abortModel = 0 := rfl
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : abortRun.outcome = .error .initialAdversaryAbort := rfl
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : abortRun.trace.oracleQueries = 1 := rfl
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : abortRun.trace.stateRestores = 0 := rfl
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (treePlan 0).bound (model 0) (initialSnapshot (model 0)) (.scalar 0 0) (st 0) = 0 := rfl

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def extractedZero : Bool := match (run 0).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed (claim 0) f with
    | .relation _ => false
    | .witness w => decide (w = (⟨fun _ => 0,fun _ => 0,0⟩ :
      CryptoHiddenScalarInnerProductProtocolContract.Witness 37 0))
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : extractedZero = true := by decide +kernel
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (run 2).trace.oracleQueries ≤ scheduleFuel ((plan 2).decode (model 2) (seed 2)) :=
  (resource_bounds _ _ _).1
set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬(∀ a : Z, Prob.probability Finset.univ
    (Finset.univ.filter fun i : Fin 8 => (calls8 i : Z)^2 = a) ≤ (1/10 : ℚ)) := by decide +kernel

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def checks : List Bool := [
 decide ((treePlan 1).bound (model 1) (initialSnapshot (model 1)) (.round ⟨0,0⟩) (st 1) = 105/256),
 decide ((etaPlan 1).bound (claim 1) (model 1) (initialSnapshot (model 1)) ann 0 0 = 4305/65536),
 decide ((plan 1).bound (claim 1) (model 1) = 2030724465/281474976710656),
 (run 0).outcome.isOk, (run 1).outcome.isOk, (run 2).outcome.isOk,
 decide (fiveActual = 6/125), decide (quota 3 3 (3/5) (3/10) = 0),
 decide ((treePlan 0).bound memModel leaf0.after leaf0.packet memSt = 1),
 decide ((treePlan 0).bound memModel leaf1.after leaf1.packet memSt = 0),
 (match repeated.outcome with | .error e => e == .exhaustedE | _ => false), !repeated.trace.isEmpty,
 decide ((plan 1).bound (claim 1) abortModel = 0),
 (match abortRun.outcome with | .error e => e == .initialAdversaryAbort | _ => false),
 extractedZero,
 (run 0).trace.oracleQueries == 10, (run 1).trace.oracleQueries == 34,
 (run 2).trace.oracleQueries == 130, (run 2).trace.stateRestores == 129,
 repeated.trace.candidateRejections == 2,
 abortRun.trace.oracleQueries == 1, abortRun.trace.stateRestores == 0]
end ForkRecursiveQuotaRegression

set_option maxHeartbeats 1600000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let cs := ForkRecursiveQuotaRegression.checks
  unless cs.all id do throw (IO.userError s!"recursive quota failures: {cs}")
  IO.println s!"FORK_RECURSIVE_QUOTA_OK {cs.length}"

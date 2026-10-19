import Verification.CryptoHiddenScalarForkScheduleProgressContract
namespace ForkScheduleRegression
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkScheduleProgressContract
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

abbrev U := Fin 4
def C4 : Finset U := Finset.univ
def trial (u : U) : Attempt U := ⟨if u.val < 2 then some u else none,[.query]⟩
theorem coherent : KeyCoherent id id trial := by
  intro i v h
  dsimp [trial] at h
  split at h
  · simpa using (Option.some.inj h).symm
  · simp at h

theorem good_density : (1/2 : ℚ) ≤ Prob.probability C4 (successSeeds C4 id trial) := by decide +kernel
theorem class_cap : ∀ x, Prob.probability C4 (classSeeds C4 id id x) ≤ (1/4 : ℚ) := by decide +kernel
def rates (j : ℕ) : ℚ := max 0 (1/2 - (j : ℚ)*(1/4))
def D2 := Product.productTapes C4 2
def succeeds (w : Fin 2 → U) := (collect 2 id id trial (iidSchedule id w)).value.isSome

theorem bounds (T : ℕ) : ProgressBounds (Product.productTapes C4 T)
    (scanCounts 2 id id trial (iidSchedule id)) 2 T rates := by
  exact iid_progress_bounds 2 C4 (by decide) id id id trial
    coherent (1/2) (1/4) (by norm_num) (by norm_num) (by norm_num) good_density class_cap T
example : quotaLower 2 rates 2 0 = 1/8 := by decide +kernel
example : Prob.probability D2 (D2.filter (fun w => succeeds w)) = 1/8 := by decide +kernel
example : quotaLower 2 rates 2 0 ≤ Prob.probability D2 (D2.filter (fun w => succeeds w)) := by
  exact iid_collect_probability_lower 2 C4
    (by decide) id id id trial coherent (1/2) (1/4) (by norm_num) (by norm_num)
    (by norm_num) good_density class_cap 2
example : quotaLower 2 rates 1 0 = 0 := quota_insufficient _ _ _ _ (by decide)
example : quotaLower 0 rates 0 0 = 1 := rfl
example : (Product.productTapes (∅ : Finset U) 1).Nonempty = False := by decide +kernel
example : (Product.productTapes (∅ : Finset U) 0).card = 1 := by decide +kernel
example (w : Fin 2 → U) (u : U) :
    (iidSchedule id (Function.update w 1 u)).take 1 = (iidSchedule id w).take 1 :=
  schedule_prefix_update id w 1 u
example : ((D2.filter fun w => w 0 = 0 ∧ w 1 = 1).card : ℚ) / (D2.filter fun w => w 0 = 0).card = 1/4 := by decide +kernel
example : (D2.filter (fun w => w 0 = 0 ∧ w 1 ∈ ({1} : Finset U))).card * C4.card =
    (D2.filter (fun w => w 0 = 0)).card * (C4 ∩ {1}).card := by
  exact fresh_event_count C4 2 1 (fun w => w 0 = 0) (by intro w u; simp) {1}
example : Prob.probability C4 (blockedSeeds C4 id id {0,1}) ≤ (2 : ℚ)*(1/4) := by
  simpa using blocked_mass_le C4 (by decide) id id {0,1} (1/4) class_cap
example : Prob.probability C4 (successSeeds C4 id trial \ blockedSeeds C4 id id {0,1}) = 0 := by decide +kernel

-- A different sampling law: remove diagonals, without pretending it is iid.
def withoutReplacement := D2.filter fun w => w 0 ≠ w 1
example : Prob.probability withoutReplacement (withoutReplacement.filter (fun w => succeeds w)) = 1/6 := by decide +kernel
example : Prob.probability withoutReplacement (withoutReplacement.filter (fun w => succeeds w)) ≠
    Prob.probability D2 (D2.filter (fun w => succeeds w)) := by decide +kernel

-- Microseed multiplicities must be retained, not replaced by uniform image.
def weighted (u : U) : Bool := u.val < 3
example : Prob.probability C4 (classSeeds C4 weighted id true) = 3/4 := by decide +kernel
example : Prob.probability (C4.image weighted) {true} = 1/2 := by decide +kernel
example : ¬(∀ k, Prob.probability C4 (classSeeds C4 weighted id k) ≤ (1/2 : ℚ)) := by decide +kernel
example : ∀ k, Prob.probability C4 (classSeeds C4 weighted id k) ≤ (3/4 : ℚ) := by decide +kernel

def child (p : Nat × Bool) : Attempt Nat := ⟨if p.2 then some p.1 else none,[.query]⟩
example : (collect 2 Prod.fst id child [(0,false),(0,true),(1,true)]).value.isSome = true := by decide +kernel
example : (collect 2 Prod.fst id child [(0,true),(0,true)]).value.isSome = false := by decide +kernel
example : (collect 1 Prod.fst id child [(0,true),(1,false)]).trace = [.restore,.query] := rfl
def correlated (w : Bool) := [(0,w),(0,w)]
example : ¬ProgressBounds (Finset.univ : Finset Bool)
    (scanCounts 1 Prod.fst id child correlated) 1 2 (fun _ => 1/2) := by decide +kernel
example : Prob.probability (Finset.univ : Finset Bool)
    (Finset.univ.filter fun b => (collect 1 Prod.fst id child (correlated b)).value.isSome) = 1/2 := by decide +kernel

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev Z := ZMod 11
def units : Finset Zˣ := Finset.univ
def squareTrial (u : Zˣ) : Attempt Z := ⟨some ((u : Z)^2),[]⟩
theorem squareCoherent : KeyCoherent (fun u : Zˣ => (u : Z)^2) id squareTrial := by
  intro u v h
  exact (Option.some.inj h).symm
example : ∀ x : Z, (classSeeds units id (fun u => (u : Z)^2) x).card ≤ 2 := by decide +kernel
example : ∀ x : Z, Prob.probability units (classSeeds units id (fun u => (u : Z)^2) x) ≤ (1/5 : ℚ) := by decide +kernel
example (T : ℕ) : ProgressBounds (Product.productTapes units T)
    (scanCounts 4 (fun u : Zˣ => (u : Z)^2) id squareTrial (iidSchedule id)) 4 T
    (fun j => max 0 (1-(j : ℚ)*(1/5))) :=
  iid_progress_bounds 4 units (by decide) id _ id squareTrial squareCoherent 1 (1/5)
    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) T
example : quotaLower 4 (fun j => max 0 (1-(j : ℚ)*(1/5))) 4 0 = 24/125 := by decide +kernel
example : quotaLower 4 (fun j => max 0 (1-(j : ℚ)*(1/3))) 7 0 = 0 := by decide +kernel
example : ((Finset.univ : Finset (ZMod 7)ˣ).image (fun u : (ZMod 7)ˣ => (u : ZMod 7)^2)).card = 3 := by decide +kernel

-- Actual depth-one snapshot acquisition, six nonvacuous 4-leaf IPA trees.
def u2 : Zˣ := Units.mk0 2 (by decide)
def u3 : Zˣ := Units.mk0 3 (by decide)
def u4 : Zˣ := Units.mk0 4 (by decide)
def ann : F.Announcement Z := ⟨0,0,0⟩
def claim : F.Claim 11 Z 1 := ⟨⟨1,2,3,fun _ => 1,fun _ => 1⟩,0,0⟩
def model : AdversaryModel 11 Z Unit Nat :=
  ⟨(),0,fun _ s req => some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 0
    | .binding _ => .round ⟨0,0⟩ | .inner _ _ => .leaf 0 0),s.memory+1,1)⟩
def ips : IPASchedule 11 1 := [(1,()),(u2,()),(u3,()),(u4,())]
def etas : EtaSchedule 11 1 := [(1,ips),(u2,ips)]
def draw (i : Fin 3) : Z × EtaSchedule 11 1 := (i.val,etas)
def obs : Observation model (initialSnapshot model) .commit := ⟨.announcement ann,1,1,rfl⟩
def outerTrial (pr : Z × EtaSchedule 11 1) :=
  acquireNode claim model obs.after (obs.reachable .initial) ann pr.1 pr.2

theorem outerGood : (1 : ℚ) ≤ Prob.probability (Finset.univ : Finset (Fin 3))
    (successSeeds Finset.univ draw outerTrial) := by decide +kernel
theorem outerClass : ∀ x : Z, Prob.probability (Finset.univ : Finset (Fin 3))
    (classSeeds Finset.univ draw Prod.fst x) ≤ (1/3 : ℚ) := by decide +kernel
example : quotaLower 3 (fun j => max 0 (1-(j : ℚ)*(1/3))) 3 0 = 2/9 := by decide +kernel
example : ∃ w ∈ Product.productTapes (Finset.univ : Finset (Fin 3)) 3, ∃ f,
    (acquireCompressedFork claim model (iidSchedule draw w)).outcome = .ok f ∧
    ForkProvenance model f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
  iid_positive_extracts claim model obs ann rfl rfl Finset.univ (by simp) draw
    1 (1/3) (by norm_num) (by norm_num) (by norm_num) outerGood outerClass 3 (by decide +kernel)

def witnessOK : Bool := match (acquireCompressedFork claim model (iidSchedule draw id)).outcome with
  | .error _ => false
  | .ok f => match C.extractCompressed claim f with
    | .witness w => decide (w = ⟨fun _ => 0,fun _ => 0,0⟩)
    | .relation _ => false

def checks : List Bool := [
  decide (quotaLower 2 rates 2 0 = 1/8), decide (Prob.probability D2 (D2.filter (fun w => succeeds w)) = 1/8),
  decide (Prob.probability withoutReplacement (withoutReplacement.filter (fun w => succeeds w)) = 1/6),
  decide (Prob.probability C4 (classSeeds C4 weighted id true) = 3/4),
  decide (Prob.probability (C4.image weighted) {true} = 1/2),
  decide (ProgressBounds D2 (scanCounts 2 id id trial (iidSchedule id)) 2 2 rates),
  decide (quotaLower 2 rates 1 0 = 0), decide (quotaLower 0 rates 0 0 = 1),
  decide (Prob.probability C4 (successSeeds C4 id trial \ blockedSeeds C4 id id {0,1}) = 0),
  (collect 2 Prod.fst id child [(0,false),(0,true),(1,true)]).value.isSome,
  !(collect 2 Prod.fst id child [(0,true),(0,true)]).value.isSome,
  (collect 1 Prod.fst id child [(0,true),(1,false)]).trace.length == 2,
  decide (¬ProgressBounds (Finset.univ : Finset Bool)
    (scanCounts 1 Prod.fst id child correlated) 1 2 (fun _ => 1/2)),
  decide (quotaLower 4 (fun j => max 0 (1-(j : ℚ)*(1/5))) 4 0 = 24/125),
  decide (quotaLower 4 (fun j => max 0 (1-(j : ℚ)*(1/3))) 7 0 = 0),
  decide (quotaLower 3 (fun j => max 0 (1-(j : ℚ)*(1/3))) 3 0 = 2/9), witnessOK,
  (acquireCompressedFork claim model (iidSchedule draw id)).trace.oracleQueries == 34,
  (acquireCompressedFork claim model (iidSchedule draw id)).trace.stateRestores == 33,
  (Product.productTapes C4 2).card == 16,
  (Product.productTapes C4 0).card == 1]
end ForkScheduleRegression

def main : IO Unit := do
  let cs := ForkScheduleRegression.checks
  unless cs.all id do throw (IO.userError s!"fork schedule failures: {cs}")
  IO.println s!"FORK_SCHEDULE_OK {cs.length}"

import Verification.CryptoHiddenScalarForkLocalDensityContract
namespace ForkLocalDensityRegression
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
open CryptoHiddenScalarForkScheduleProgressContract
open CryptoHiddenScalarForkLocalDensityContract
set_option maxRecDepth 40000
set_option maxHeartbeats 800000

def bits : Finset Bool := Finset.univ
def probe (p : Bool × Bool) : Attempt Bool := ⟨if !p.1 || p.2 then some p.1 else none,[]⟩
def delta (u : Bool) : ℚ := if u then 1/2 else 1
theorem coherent : KeyCoherent Prod.fst id probe := by
  intro p v h
  dsimp [probe] at h
  split at h
  · exact (Option.some.inj h).symm
  · simp at h
example : average bits delta = 3/4 := by decide +kernel
example : Prob.probability (bits ×ˢ bits) (successSeeds (bits ×ˢ bits) id probe) = 3/4 := by decide +kernel
example : Prob.probability (bits ×ˢ bits) (successSeeds (bits ×ˢ bits) id probe) =
    average bits (fun u => Prob.probability bits (successSeeds bits (fun v => (u,v)) probe)) :=
  full_probe_rate_eq_average bits bits Prod.mk probe
theorem child_bound : ∀ u ∈ bits, delta u ≤ Prob.probability bits (successSeeds bits (fun v => (u,v)) probe) := by decide +kernel
example : average bits delta ≤ Prob.probability (bits ×ˢ bits) (successSeeds (bits ×ˢ bits) id probe) :=
  full_probe_density_lower bits bits Prod.mk probe delta child_bound
example : (1/2 : ℚ)*1 ≤ Prob.probability (bits ×ˢ bits) (successSeeds (bits ×ˢ bits) id probe) :=
  good_call_density_lower bits bits {false} (by decide) Prod.mk probe (1/2) 1
    (by norm_num) (by decide +kernel) (by decide +kernel)
example : Prob.probability (bits ×ˢ bits) (classSeeds (bits ×ˢ bits) id Prod.fst true) = 1/2 := by decide +kernel
example : Prob.probability (bits ×ˢ bits) (classSeeds (bits ×ˢ bits) id Prod.fst true) =
    Prob.probability bits (bits.filter fun u => u = true) :=
  full_probe_class_mass_eq bits bits (by decide) Prod.mk Prod.fst id (fun _ _ => rfl) true

def rates (j : ℕ) : ℚ := max 0 (3/4-(j : ℚ)*(1/2))
def space := Product.productTapes (bits ×ˢ bits) 2
example : quotaLower 2 rates 2 0 = 3/16 := by decide +kernel
example : Prob.probability space (space.filter fun w => (collect 2 Prod.fst id probe (iidSchedule id w)).value.isSome) = 1/4 := by decide +kernel
example : quotaLower 2 rates 2 0 ≤ Prob.probability space
    (space.filter fun w => (collect 2 Prod.fst id probe (iidSchedule id w)).value.isSome) :=
  by
    change quotaLower 2 (fun j => max 0 ((3/4 : ℚ)-(j : ℚ)*(1/2))) 2 0 ≤ _
    have h := averaged_collect_probability_lower 2 bits (by decide) bits (by decide)
      Prod.mk Prod.fst id probe coherent id (fun _ _ => rfl) delta
      (by decide +kernel) child_bound (1/2) (by norm_num) (by decide +kernel) 2
    simpa only [rates, space, show average bits delta = (3/4 : ℚ) by decide +kernel,
      show (fun uv : Bool × Bool => (uv.1,uv.2)) = id by funext p; cases p; rfl] using h
-- Loose but valid beta makes the conservative bound zero, while actual success is positive.
example : quotaLower 2 (fun j => max 0 (3/4-(j : ℚ))) 3 0 = 0 := by decide +kernel
example : 0 < Prob.probability space (space.filter fun w => (collect 2 Prod.fst id probe (iidSchedule id w)).value.isSome) := by decide +kernel
example : 0 < quotaLower 2 rates 2 0 := linear_quota_positive 2 2 (by decide) le_rfl
  (3/4) (1/2) (by norm_num) (by norm_num) (by norm_num)
example : quotaLower 2 rates 1 0 = 0 := by decide +kernel
example : quotaLower 0 rates 0 0 = 1 := rfl
-- Correlated suffixes have uniform marginals but a different full-probe law.
def joint (u : Bool) := (u,!u)
example : Prob.probability bits (successSeeds bits joint probe) = 1/2 := by decide +kernel
example : ¬(average bits delta ≤ Prob.probability bits (successSeeds bits joint probe)) := by decide +kernel
-- Multiplicity is preserved under product extension; uniform image would change beta.
def weighted (u : Fin 4) : Bool := u.val < 3
example : Prob.probability ((Finset.univ : Finset (Fin 4)) ×ˢ bits)
    (classSeeds (Finset.univ ×ˢ bits) (fun uv => (weighted uv.1,uv.2)) Prod.fst true) = 3/4 := by decide +kernel
example : Prob.probability ((Finset.univ : Finset (Fin 4)).image weighted) {true} = 1/2 := by decide +kernel
example : ¬(∅ : Finset Bool).Nonempty := by decide
example : average (∅ : Finset Bool) delta = 0 := by simp [average]

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev Z := ZMod 11
def ann : F.Announcement Z := ⟨0,0,0⟩
def claim0 : F.Claim 11 Z 0 := ⟨⟨1,1,1,fun _ => 1,fun _ => 1⟩,0,0⟩
def memModel : AdversaryModel 11 Z Unit Bool := ⟨(),false,fun _ s req => match req with
  | .commit => some (.announcement ann,false,1)
  | .outer e => some (.scalar 0 0, e != 0,1)
  | .binding _ => some (.leaf (if s.memory then 1 else 0) 0,s.memory,1)
  | .inner _ _ => none⟩
def initObs : Observation memModel (initialSnapshot memModel) .commit := ⟨.announcement ann,false,1,rfl⟩
def e0Obs : Observation memModel initObs.after (.outer 0) := ⟨.scalar 0 0,false,1,rfl⟩
def e1Obs : Observation memModel initObs.after (.outer 1) := ⟨.scalar 0 0,true,1,rfl⟩
example : ReachableSnapshot memModel e0Obs.after := e0Obs.reachable (initObs.reachable .initial)
example : ReachableSnapshot memModel e1Obs.after := e1Obs.reachable (initObs.reachable .initial)
example : C.responseClaim claim0 ann 0 0 = C.responseClaim claim0 ann 1 0 := by decide +kernel
example : etaChildRate claim0 memModel e0Obs.after (e0Obs.reachable (initObs.reachable .initial)) ann 0 0
    ({()} : Finset Unit) 1 (fun _ => ()) = 1 := by decide +kernel
example : etaChildRate claim0 memModel e1Obs.after (e1Obs.reachable (initObs.reachable .initial)) ann 1 0
    ({()} : Finset Unit) 1 (fun _ => ()) = 0 := by decide +kernel
-- Exact depth-one collector, all child vectors zero; masks and calls are not reseeded.
def u2 : Zˣ := Units.mk0 2 (by decide)
def u3 : Zˣ := Units.mk0 3 (by decide)
def u4 : Zˣ := Units.mk0 4 (by decide)
def claim : F.Claim 11 Z 1 := ⟨⟨1,2,3,fun _ => 1,fun _ => 1⟩,0,0⟩
def model : AdversaryModel 11 Z Unit Nat :=
  ⟨(),0,fun _ s req => some ((match req with
    | .commit => .announcement ann | .outer _ => .scalar 0 0
    | .binding _ => .round ⟨0,0⟩ | .inner _ _ => .leaf 0 0),s.memory+1,1)⟩
def ips : IPASchedule 11 1 := [(1,()),(u2,()),(u3,()),(u4,())]
def etas : EtaSchedule 11 1 := [(1,ips),(u2,ips)]
def obs : Observation model (initialSnapshot model) .commit := ⟨.announcement ann,1,1,rfl⟩
def calls (i : Fin 3) : Z := i.val
def children (_ : Fin 3) (_ : Unit) := etas
def avg := average (Finset.univ : Finset (Fin 3)) (fun _ => (1 : ℚ))
theorem childGood : ∀ u ∈ (Finset.univ : Finset (Fin 3)), (1 : ℚ) ≤
    outerChildRate claim model obs.after (obs.reachable .initial) ann {()} (calls u) (children u) := by decide +kernel
example : avg = 1 := by decide +kernel
example : ∀ a : Z, Prob.probability (Finset.univ : Finset (Fin 3))
    (Finset.univ.filter fun u => calls u = a) ≤ (1/3 : ℚ) := by decide +kernel
theorem acquisition_bound : quotaLower 3 (fun j => max 0 (avg-(j : ℚ)*(1/3))) 3 0 ≤
    Prob.probability (Product.productTapes ((Finset.univ : Finset (Fin 3)) ×ˢ {()}) 3)
      ((Product.productTapes (Finset.univ ×ˢ {()}) 3).filter fun w =>
        (acquireCompressedFork claim model (iidSchedule (fun uv => (calls uv.1, children uv.1 uv.2)) w)).outcome.isOk) :=
  averaged_acquisition_probability_lower claim model obs ann rfl rfl Finset.univ (by simp)
    {()} (by simp) calls children (fun _ => 1) (by norm_num) childGood (1/3)
    (by norm_num) (by decide +kernel) 3
example : quotaLower 3 (fun j => max 0 (avg-(j : ℚ)*(1/3))) 3 0 = 2/9 := by decide +kernel
example : ∃ w ∈ Product.productTapes ((Finset.univ : Finset (Fin 3)) ×ˢ {()}) 3, ∃ f,
    (acquireCompressedFork claim model (iidSchedule (fun uv => (calls uv.1,children uv.1 uv.2)) w)).outcome = .ok f ∧
    ForkProvenance model f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
  positive_schedule_probability_extracts claim model _ _ (lt_of_lt_of_le (by decide +kernel) acquisition_bound)
example : quotaLower 2 (fun j => max 0 (24/125-(j : ℚ)*(1/10))) 2 0 = 276/15625 := by decide +kernel
example : quotaLower 3 (fun j => max 0 (276/15625-(j : ℚ)*(1/11))) 4 0 = 0 := by decide +kernel

def abortModel : AdversaryModel 11 Z Unit Unit := ⟨(),(),fun _ _ _ => none⟩
example : (acquireCompressedFork claim abortModel []).outcome = .error .initialAdversaryAbort := rfl
example : outerChildRate claim abortModel (initialSnapshot abortModel) .initial ann
    ({()} : Finset Unit) 0 (fun _ => etas) = 0 := rfl
def wrongModel : AdversaryModel 11 Z Unit Unit := ⟨(),(),fun _ _ _ => some (.leaf 0 0,(),0)⟩
example : outerChildRate claim wrongModel (initialSnapshot wrongModel) .initial ann
    ({()} : Finset Unit) 0 (fun _ => etas) = 0 := rfl
def invalidModel : AdversaryModel 11 Z Unit Unit := ⟨(),(),fun _ _ _ => some (.scalar 1 0,(),0)⟩
example : outerChildRate claim invalidModel (initialSnapshot invalidModel) .initial ann
    ({()} : Finset Unit) 0 (fun _ => etas) = 0 := by decide +kernel

def eObs : Observation model obs.after (.outer 0) := ⟨.scalar 0 0,2,1,rfl⟩
def etaObs : Observation model eObs.after (.binding 1) := ⟨.round ⟨0,0⟩,3,1,rfl⟩
def st := P.toIPA (C.responseClaim claim ann 0 0) 1
example : average ({()} : Finset Unit) (fun _ => (1 : ℚ)) ≤
    Prob.probability (({()} : Finset Unit) ×ˢ ({()} : Finset Unit))
      (successSeeds ({()} ×ˢ {()}) (fun _ => ((1 : Zˣ),()))
        (roundAttempt model etaObs.after (etaObs.reachable (eObs.reachable (obs.reachable .initial))) st ⟨0,0⟩)) :=
  round_density_lower model etaObs.after (etaObs.reachable (eObs.reachable (obs.reachable .initial)))
    st ⟨0,0⟩ {()} {()} (fun _ => 1) (fun _ _ => ()) (fun _ => 1) (by decide +kernel)
example : average ({()} : Finset Unit) (fun _ => (1 : ℚ)) ≤
    Prob.probability (({()} : Finset Unit) ×ˢ ({()} : Finset Unit))
      (successSeeds ({()} ×ˢ {()}) (fun _ => ((1 : Zˣ),ips))
        (etaAttempt claim model eObs.after (eObs.reachable (obs.reachable .initial)) ann 0 0)) :=
  eta_density_lower claim model eObs.after (eObs.reachable (obs.reachable .initial)) ann 0 0
    {()} {()} (fun _ => 1) (fun _ _ => ips) (fun _ => 1) (by decide +kernel)

def checks : List Bool := [
  decide (average bits delta = 3/4),
  decide (Prob.probability (bits ×ˢ bits) (successSeeds (bits ×ˢ bits) id probe) = 3/4),
  decide (quotaLower 2 rates 2 0 = 3/16),
  decide (Prob.probability space (space.filter fun w => (collect 2 Prod.fst id probe (iidSchedule id w)).value.isSome) = 1/4),
  decide (quotaLower 2 (fun j => max 0 (3/4-(j : ℚ))) 3 0 = 0),
  decide (Prob.probability bits (successSeeds bits joint probe) = 1/2),
  decide (Prob.probability ((Finset.univ : Finset (Fin 4)).image weighted) {true} = 1/2),
  decide (avg = 1),
  decide (etaChildRate claim0 memModel e0Obs.after (e0Obs.reachable (initObs.reachable .initial)) ann 0 0 {()} 1 (fun _ => ()) = 1),
  decide (etaChildRate claim0 memModel e1Obs.after (e1Obs.reachable (initObs.reachable .initial)) ann 1 0 {()} 1 (fun _ => ()) = 0),
  decide (quotaLower 2 (fun j => max 0 (24/125-(j : ℚ)*(1/10))) 2 0 = 276/15625),
  decide (quotaLower 3 (fun j => max 0 (276/15625-(j : ℚ)*(1/11))) 4 0 = 0)]
end ForkLocalDensityRegression

def main : IO Unit := do
  let cs := ForkLocalDensityRegression.checks
  unless cs.all id do throw (IO.userError s!"local density failures: {cs}")
  IO.println s!"FORK_LOCAL_DENSITY_OK {cs.length}"

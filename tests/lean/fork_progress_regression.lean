import Verification.CryptoHiddenScalarForkProgressProbabilityContract
namespace ForkProgressRegression
open CryptoHiddenScalarForkAcquisitionContract
open CryptoHiddenScalarForkProgressProbabilityContract
set_option maxRecDepth 40000

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def coin (pr : Nat × Bool) : Attempt Nat := if pr.2 then
  ⟨some pr.1,[.query]⟩ else ⟨none,[.query,.rejected .adversaryAbort]⟩
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem coherent : KeyCoherent Prod.fst id coin := by
  intro i v hv
  unfold coin at hv
  split at hv
  · simpa using (Option.some.inj hv).symm
  · simp at hv
abbrev Bits := Fin 3 → Bool
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def probes (w : Bits) : List (Nat × Bool) :=
  [(0,w 0),(if w 0 then 1 else 0,w 1),((if w 0 then 1 else 0)+(if w 1 then 1 else 0),w 2)]
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def rates (_ : Nat) : ℚ := 1/2
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def counts := scanCounts 2 Prod.fst id coin probes
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def success (w : Bits) := (collect 2 Prod.fst id coin (probes w)).value.isSome
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def cleanEvent (w : Bits) : Bool :=
  (collect 2 Prod.fst id coin (probes w)).trace.all (fun e => match e with
    | .query | .restore => true | _ => false)

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem coin_bounds : ProgressBounds (Finset.univ : Finset Bits) counts 2 3 rates
  := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 2 rates 3 0 = 1/2 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 2 rates 2 0 = 1/4 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Prob.probability (Finset.univ : Finset Bits) (Finset.univ.filter (fun w => success w)) =
  1/2 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Prob.probability (Finset.univ : Finset Bits) (Finset.univ.filter (fun w => cleanEvent w))
  = 1/4 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 2 rates 3 0 ≤ Prob.probability (Finset.univ : Finset Bits)
    (Finset.univ.filter (fun w => success w)) :=
  collect_probability_lower 2 Prod.fst id coin coherent _ (by simp) probes 3
    (by intro w _; rfl) rates coin_bounds
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : CountLaws (Finset.univ : Finset Bits) counts 2 3 :=
  scan_count_laws 2 Prod.fst id coin coherent _ probes 3
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 0 rates 0 0 = 1 := rfl
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 3 rates 2 0 = 0 := quota_insufficient _ _ _ _ (by decide)
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (p : Nat → ℚ) (T : Nat) : quotaLower 1 p T 0 = 1-(1-p 0)^T := quota_one p T
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 4 (fun _ => 1) 4 0 = 1 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 4 (fun _ => 0) 4 0 = 0 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 2 (fun j => if j=0 then 1 else 0) 8 0 = 0 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : retainedCount 2 Prod.fst id coin [(7,false),(7,true),(8,true)] 3 = 2 := rfl
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (collect 2 Prod.fst id coin [(7,false),(7,true),(8,true)]).value.isSome = true
  := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (collect 2 Prod.fst id coin [(7,true),(7,true)]).value.isSome = false := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (collect 1 Prod.fst id coin [(7,true),(8,false)]).trace = [.restore,.query] := rfl

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def incoherent (_ : Nat) : Attempt Nat := ⟨some 0,[.query]⟩
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : retainedCount 2 id id incoherent [0,1] 2 = 2 := rfl
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (collect 2 id id incoherent [0,1]).value.isSome = false := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬KeyCoherent id id incoherent := by
  intro h
  have he := h 1 0 rfl
  norm_num at he

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def correlated (w : Bool) := [(0,w),(0,w)]
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ProgressBounds (Finset.univ : Finset Bool)
    (scanCounts 1 Prod.fst id coin correlated) 1 2 rates := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : Prob.probability (Finset.univ : Finset Bool)
    (Finset.univ.filter fun w => (collect 1 Prod.fst id coin (correlated w)).value.isSome) = 1/2
      := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : max 0 ((3/4 : ℚ)-1/2) ≤ Prob.probability (Finset.univ : Finset (Fin 4))
    ({0,1,2} \ {1,2}) := unblocked_probability_lower _ _ _ (by simp)
      (by simp) (by simp) _ _ (by decide +kernel) (by decide +kernel)
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ProgressBounds (∅ : Finset Bits) counts 2 3 rates := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 2 rates 3 0 ≤ quotaLower 2 rates 3 1 := quota_step_mono _ _
    (by intro j _; norm_num [rates]) _ _

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev Z := ZMod 11
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def u2 : Zˣ := Units.mk0 2 (by decide)
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def u3 : Zˣ := Units.mk0 3 (by decide)
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def u4 : Zˣ := Units.mk0 4 (by decide)
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ann : F.Announcement Z := ⟨0,0,0⟩
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def claim : F.Claim 11 Z 1 := ⟨⟨1,2,3,fun _ => 1,fun _ => 1⟩,0,0⟩
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def model : AdversaryModel 11 Z Unit Nat :=
  ⟨(),0,fun _ s req => some ((match req with
    | .commit => .announcement ann
    | .outer _ => .scalar 0 0
    | .binding _ => .round ⟨0,0⟩
    | .inner _ _ => .leaf 0 0),s.memory+1,1)⟩
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def ips : IPASchedule 11 1 := [(1,()),(u2,()),(u3,()),(u4,())]
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def etas : EtaSchedule 11 1 := [(1,ips),(u2,ips)]
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def schedule (b : Bool) : ProbeSchedule 11 1 := if b then
  [(0,[]),(0,etas),(1,etas),(2,etas)] else [(0,etas),(1,etas),(2,etas),(3,[])]
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def commitObs : Observation model (initialSnapshot model) .commit :=
  ⟨.announcement ann,1,1,rfl⟩
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerRates (j : Nat) : ℚ := if j=0 then 1/2 else 1
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def outerCounts := scanCounts 3 Prod.fst (fun v => v.val.challenge)
  (fun pr => acquireNode claim model commitObs.after (commitObs.reachable .initial) ann pr.1 pr.2)
    schedule

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
theorem outer_bounds : ProgressBounds (Finset.univ : Finset Bool) outerCounts 3 4 outerRates
  := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 3 outerRates 4 0 = 3/4 := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (acquireCompressedFork claim model (schedule true)).outcome.isOk = true
  := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (acquireCompressedFork claim model (schedule true)).trace.subtreeFailures = 1
  := by decide +kernel
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : quotaLower 3 outerRates 4 0 ≤ Prob.probability (Finset.univ : Finset Bool)
    (Finset.univ.filter fun b => (acquireCompressedFork claim model (schedule b)).outcome.isOk) :=
  acquisition_progress_probability_lower claim model commitObs ann rfl rfl _ (by simp)
    schedule 4 (by intro b _; cases b <;> rfl) outerRates outer_bounds
set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ∃ w ∈ (Finset.univ : Finset Bool), ∃ f,
    (acquireCompressedFork claim model (schedule w)).outcome = .ok f ∧
    ForkProvenance model f ∧ F.ResultValid claim (C.extractCompressed claim f) :=
  positive_progress_extracts claim model commitObs ann rfl rfl _ (by simp) schedule 4
    (by intro b _; cases b <;> rfl) outerRates outer_bounds (by decide +kernel)

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
/-- Direct witness checks supplement the existential composition theorem. -/
def witnessOK (b : Bool) : Bool := match (acquireCompressedFork claim model (schedule b)).outcome
  with
  | .error _ => false
  | .ok f => match C.extractCompressed claim f with
    | .witness w => decide (w = ⟨fun _ => 0,fun _ => 0,0⟩)
    | .relation _ => false

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def checks : List Bool := [
  decide (quotaLower 2 rates 3 0 = 1/2), decide (quotaLower 2 rates 2 0 = 1/4),
  decide (Prob.probability (Finset.univ : Finset Bits) (Finset.univ.filter (fun w => success w)) =
    1/2),
  decide (Prob.probability (Finset.univ : Finset Bits) (Finset.univ.filter (fun w => cleanEvent w))
    = 1/4),
  decide (ProgressBounds (Finset.univ : Finset Bits) counts 2 3 rates),
  decide (ProgressBounds (Finset.univ : Finset Bool) outerCounts 3 4 outerRates),
  (collect 2 Prod.fst id coin [(7,false),(7,true),(8,true)]).value.isSome,
  !(collect 2 Prod.fst id coin [(7,true),(7,true)]).value.isSome,
  !(collect 2 id id incoherent [0,1]).value.isSome,
  decide (¬ProgressBounds (Finset.univ : Finset Bool) (scanCounts 1 Prod.fst id coin correlated) 1
    2 rates),
  witnessOK true, witnessOK false,
  (acquireCompressedFork claim model (schedule true)).trace.subtreeFailures == 1,
  (acquireCompressedFork claim model (schedule false)).trace.subtreeFailures == 0,
  decide (quotaLower 3 outerRates 4 0 = 3/4),
  decide (quotaLower 0 rates 0 0 = 1), decide (quotaLower 3 rates 2 0 = 0),
  decide (quotaLower 4 (fun _ => 1) 4 0 = 1),
  (collect 1 Prod.fst id coin [(7,true),(8,false)]).trace.length == 2,
  (acquireCompressedFork claim model (schedule false)).trace.oracleQueries == 34,
  (acquireCompressedFork claim model (schedule true)).trace.oracleQueries == 35]
end ForkProgressRegression

set_option maxHeartbeats 16000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let cs := ForkProgressRegression.checks
  unless cs.all id do throw (IO.userError s!"fork progress failures: {cs}")
  IO.println s!"FORK_PROGRESS_OK {cs.length}"

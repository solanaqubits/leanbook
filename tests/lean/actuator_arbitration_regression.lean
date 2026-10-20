import Verification.ActuatorArbitrationContract
open ActuatorArbitrationContract

-- Pure formal fixtures, not live devices, accepted signatures or the SimLab 55 cases.
def allow : Request → Bool := fun _ => true
def start : State := { initial with
  actuator := ExternalActuatorContract.recover (ExternalActuatorContract.reserve
    ExternalActuatorContract.initial 7)
  usedGrants := [70] }
def keep : Request := ⟨1, 10, ⟨0, 0⟩, 100, .keepLocked⟩
def ready : Request := ⟨2, 11, ⟨0, 1⟩, 200, .restoreReadiness 5⟩
def newAction : Request := ⟨3, 12, ⟨0, 2⟩, 300, .authorizeNewAction 8 7 70 80⟩
def kept : State := (applyRequest allow start keep).1
def readied : State := (applyRequest allow kept ready).1
def issued : State := (applyRequest allow readied newAction).1
def clearGrant : Request := ⟨4, 12, ⟨1, 3⟩, 400, .keepLocked⟩
def cleared : State := (applyRequest allow issued clearGrant).1

example : (applyRequest allow start keep).2 = .accepted none := by decide
example : kept.resourceVersion = 1 := by decide
example : kept.caseVersion 10 = 1 ∧ kept.caseVersion 11 = 0 := by decide
example : (applyRequest allow kept keep).2 = .replayed none := by decide
example : (applyRequest allow kept {keep with context := 101}).2 = .conflictingReplay := by decide
example : (applyRequest allow kept {keep with expected := ⟨1,1⟩}).2 = .conflictingReplay := by decide
example : (applyRequest allow kept {keep with reqID := 20, caseID := 11}).2 = .versionConflict := by decide
example : (applyRequest allow kept {ready with expected := ⟨1,1⟩}).2 = .versionConflict := by decide
example : (applyRequest (fun _ => false) kept ready).2 = .unauthorized := by decide
example : (applyRequest allow kept ready).2 = .accepted none := by decide
example : readied.readiness = 5 ∧ readied.activeGrant = none := by decide
example : readied.actuator.journal 7 = some .armed ∧ readied.actuator.permit 7 = false := by decide
example : (applyRequest allow readied newAction).2 = .accepted (some 80) := by decide
example : (applyRequest allow readied {newAction with decision := .authorizeNewAction 7 7 70 80}).2
    = .invalidAction := by decide
example : (applyRequest allow readied {newAction with decision := .authorizeNewAction 8 7 70 70}).2
    = .invalidAction := by decide
example : (applyRequest allow readied {newAction with decision := .authorizeNewAction 8 99 70 80}).2
    = .invalidAction := by decide
example : issued.lineage = [⟨3,8,7,70,80⟩] := by decide
example : issued.actuator.permit 8 = false ∧ issued.actuator.journal 8 = none := by decide
example : issued.usedGrants = [80,70] := by decide
example : (applyRequest allow issued newAction).2 = .replayed (some 80) := by decide
example : cleared.activeGrant = none := by decide
example : (applyRequest allow cleared newAction).2 = .replayed (some 80) := by decide
example : (applyRequest allow cleared newAction).1.activeGrant = none := by decide
example : (applyRequest allow cleared {newAction with reqID := 30, expected := ⟨2,4⟩, decision := .authorizeNewAction 9 7 70 80}).2 = .invalidAction := by decide
example : (applyRequest allow cleared {newAction with reqID := 30, expected := ⟨2,4⟩, decision := .authorizeNewAction 8 7 70 90}).2 = .invalidAction := by decide
example : cleared.lineage = issued.lineage := by decide
example : (applyRequest (fun _ => false) cleared newAction).2 = .replayed (some 80) := by decide

-- Recovering an old receipt under a changed policy grants no present authority.
example (policy : Request → Bool) (s t : State) (rs : List Request)
    (h : Run policy s rs t) (hu : 70 ∈ s.usedGrants) (hi : s.activeGrant ≠ some 70) :
    t.activeGrant ≠ some 70 := inactive_old_grant_stays_inactive h hu hi
example (policy : Request → Bool) (auth conf : Nat → Prop) (t : State)
    (es : List (ExternalActuatorContract.Event Nat))
    (h : CombinedRun policy auth conf initial es t) :
    ExternalActuatorContract.dispatchCount es 7 ≤ 1 := combined_at_most_one_dispatch h 7

-- Finite checks of request conflicts and resource-CAS; no cryptographic/physical oracle.
def main : IO Unit := do
  let mut checked := 0
  for context in List.range 16 do
    let req := { keep with context := context }
    if (applyRequest allow kept req).2 != .conflictingReplay then
      throw (IO.userError "changed context must conflict")
    checked := checked + 1
  for c in List.range 16 do
    let req := { keep with reqID := 100+c, caseID := c }
    if (applyRequest allow kept req).2 != .versionConflict then
      throw (IO.userError "stale shared resource must conflict for every case")
    checked := checked + 1
  if (applyRequest allow cleared newAction).1.activeGrant != none then
    throw (IO.userError "receipt replay restored a cleared grant")
  checked := checked + 1
  IO.println s!"ACTUATOR_ARBITRATION_OK {checked}"

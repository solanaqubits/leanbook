/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.ExternalActuatorContract

/-! Serialized arbitration for one resource, with many cases. Natural-number IDs are
abstract labels, not cryptographic encodings. `policy` is an explicit external decision
validator, not evidence of PKI, safe mechanics or trusted persistence. A fresh commit
models atomic decision/grant registration; it does not install readiness on hardware
or dispatch a command. Exact replay returns a receipt and never restores active authority.
-/
namespace ActuatorArbitrationContract

structure VersionPair where
  caseVersion : Nat
  resourceVersion : Nat
  deriving DecidableEq, Repr

inductive Decision where
  | keepLocked
  | restoreReadiness (mask : Nat)
  | authorizeNewAction (action parent predecessorGrant grant : Nat)
  deriving DecidableEq, Repr

/-- `context` represents the entire immutable policy/evidence/intent context. A concrete
codec must bind every relevant field injectively; equality of hashes is not proved here. -/
structure Request where
  reqID : Nat
  caseID : Nat
  expected : VersionPair
  context : Nat
  decision : Decision
  deriving DecidableEq, Repr

structure Receipt where
  request : Request
  grant : Option Nat
  deriving DecidableEq, Repr

structure Lineage where
  reqID : Nat
  action : Nat
  parent : Nat
  predecessorGrant : Nat
  grant : Nat
  deriving DecidableEq, Repr

structure State where
  actuator : ExternalActuatorContract.State Nat
  caseVersion : Nat → Nat
  resourceVersion : Nat
  readiness : Nat
  activeGrant : Option Nat
  receipts : Nat → Option Receipt
  usedGrants : List Nat
  allocatedActions : List Nat
  lineage : List Lineage

def initial : State :=
  ⟨ExternalActuatorContract.initial, fun _ => 0, 0, 0, none, fun _ => none, [], [], []⟩

def resultGrant (r : Request) : Option Nat :=
  match r.decision with
  | .authorizeNewAction _ _ _ grant => some grant
  | _ => none

def versions (s : State) (r : Request) : VersionPair :=
  ⟨s.caseVersion r.caseID, s.resourceVersion⟩

/-- Old journal entries and all previously allocated IDs are excluded. The caller's
policy must additionally validate predecessor-grant ownership and semantic safety. -/
def FreshAction (s : State) (r : Request) : Prop :=
  match r.decision with
  | .authorizeNewAction a p pg g =>
      a ≠ p ∧ s.actuator.journal a = none ∧ s.actuator.journal p ≠ none ∧
      a ∉ s.allocatedActions ∧ g ∉ s.usedGrants ∧ g ≠ pg
  | _ => True

instance (s : State) (r : Request) : Decidable (FreshAction s r) := by
  unfold FreshAction
  split <;> infer_instance

/-- Private update kernel: callers must satisfy FreshCommit via `applyRequest`.
Every fresh decision advances the shared resource version, including keepLocked. -/
def commit (s : State) (r : Request) : State :=
  { s with
    caseVersion := fun c => if c = r.caseID then s.caseVersion c + 1 else s.caseVersion c
    resourceVersion := s.resourceVersion + 1
    readiness := match r.decision with | .restoreReadiness m => m | _ => s.readiness
    activeGrant := resultGrant r
    receipts := fun q => if q = r.reqID then some ⟨r, resultGrant r⟩ else s.receipts q
    usedGrants := match resultGrant r with | some g => g :: s.usedGrants | none => s.usedGrants
    allocatedActions := match r.decision with
      | .authorizeNewAction a _ _ _ => a :: s.allocatedActions | _ => s.allocatedActions
    lineage := match r.decision with
      | .authorizeNewAction a p pg g => ⟨r.reqID, a, p, pg, g⟩ :: s.lineage
      | _ => s.lineage }

inductive Outcome where
  | accepted (grant : Option Nat)
  | replayed (grant : Option Nat)
  | conflictingReplay | versionConflict | unauthorized | invalidAction
  deriving DecidableEq, Repr

def applyRequest (policy : Request → Bool) (s : State) (r : Request) : State × Outcome :=
  match s.receipts r.reqID with
  | some old =>
      if old.request = r then (s, .replayed old.grant) else (s, .conflictingReplay)
  | none =>
      if r.expected ≠ versions s r then (s, .versionConflict)
      else if policy r = false then (s, .unauthorized)
      else if FreshAction s r then (commit s r, .accepted (resultGrant r))
      else (s, .invalidAction)

structure FreshCommit (policy : Request → Bool) (s : State) (r : Request) : Prop where
  absent : s.receipts r.reqID = none
  version : r.expected = versions s r
  authority : policy r = true
  fresh : FreshAction s r

theorem fresh_commit_accepted {policy s r} (h : FreshCommit policy s r) :
    applyRequest policy s r = (commit s r, .accepted (resultGrant r)) := by
  simp [applyRequest, h.absent, h.version, h.authority, h.fresh]

theorem accepted_iff {policy s r g} :
    (applyRequest policy s r).2 = .accepted g ↔
      FreshCommit policy s r ∧ g = resultGrant r := by
  constructor
  · intro h
    unfold applyRequest at h
    split at h
    · split at h <;> simp_all
    · rename_i hn
      split at h
      · simp at h
      · rename_i hv
        split at h
        · simp at h
        · rename_i ha
          split at h
          · rename_i hf
            simp only [Outcome.accepted.injEq] at h
            exact ⟨⟨hn, by simpa using hv, by simpa using ha, hf⟩, h.symm⟩
          · simp at h
  · rintro ⟨h, rfl⟩
    rw [fresh_commit_accepted h]

/-- Every call either leaves the entire state unchanged or is a checked fresh commit. -/
theorem apply_cases (policy : Request → Bool) (s : State) (r : Request) :
    (applyRequest policy s r).1 = s ∨
      (FreshCommit policy s r ∧ (applyRequest policy s r).1 = commit s r) := by
  unfold applyRequest
  split
  · split <;> exact Or.inl rfl
  · rename_i hn
    split
    · exact Or.inl rfl
    · rename_i hv
      split
      · exact Or.inl rfl
      · rename_i ha
        split
        · rename_i hf
          exact Or.inr ⟨⟨hn, by simpa using hv, by simpa using ha, hf⟩, rfl⟩
        · exact Or.inl rfl

/-- Stronger than NV-log equality: arbitration does not modify any actuator permit. -/
theorem history_preservation (policy : Request → Bool) (s : State) (r : Request) :
    (applyRequest policy s r).1.actuator = s.actuator := by
  rcases apply_cases policy s r with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; rfl

theorem no_old_permit_restoration (policy : Request → Bool) (s : State) (r : Request)
    (a : Nat) (h : s.actuator.permit a = false) :
    (applyRequest policy s r).1.actuator.permit a = false := by
  rw [history_preservation]; exact h

theorem fresh_grant_not_reused {policy s r g} (h : FreshCommit policy s r)
    (hg : resultGrant r = some g) : g ∉ s.usedGrants := by
  have hf := h.fresh
  cases hd : r.decision <;> simp_all [resultGrant, FreshAction]

/-- Old allocated grants remain recorded even when activeGrant is cleared. -/
theorem used_grants_preserved (policy : Request → Bool) (s : State) (r : Request)
    (g : Nat) (hg : g ∈ s.usedGrants) : g ∈ (applyRequest policy s r).1.usedGrants := by
  rcases apply_cases policy s r with h | ⟨_, h⟩
  · rw [h]; exact hg
  · rw [h]; cases hr : resultGrant r <;> simp [commit, hr, hg]

theorem no_old_grant_on_fresh_commit {policy s r g} (h : FreshCommit policy s r)
    (hg : g ∈ s.usedGrants) : (commit s r).activeGrant ≠ some g := by
  intro he
  exact fresh_grant_not_reused h he hg

theorem restore_readiness_isolation {policy s r mask} (h : FreshCommit policy s r)
    (hd : r.decision = .restoreReadiness mask) :
    (applyRequest policy s r).1.readiness = mask ∧
    (applyRequest policy s r).1.activeGrant = none ∧
    (applyRequest policy s r).1.caseVersion r.caseID = s.caseVersion r.caseID + 1 ∧
    (applyRequest policy s r).1.resourceVersion = s.resourceVersion + 1 ∧
    (applyRequest policy s r).1.actuator = s.actuator := by
  rw [fresh_commit_accepted h]
  simp [commit, hd, resultGrant]

theorem exact_replay {policy s r receipt} (h : s.receipts r.reqID = some receipt)
    (he : receipt.request = r) :
    applyRequest policy s r = (s, .replayed receipt.grant) := by
  simp [applyRequest, h, he]

theorem conflicting_replay {policy s r receipt} (h : s.receipts r.reqID = some receipt)
    (he : receipt.request ≠ r) :
    applyRequest policy s r = (s, .conflictingReplay) := by
  simp [applyRequest, h, he]

theorem fresh_receipt (s : State) (r : Request) :
    (commit s r).receipts r.reqID = some ⟨r, resultGrant r⟩ := by simp [commit]

theorem receipt_preservation (policy : Request → Bool) (s : State) (r : Request)
    (q : Nat) (old : Receipt) (h : s.receipts q = some old) :
    (applyRequest policy s r).1.receipts q = some old := by
  rcases apply_cases policy s r with he | ⟨hf, he⟩
  · rw [he]; exact h
  · rw [he]
    have hn : q ≠ r.reqID := by intro heq; subst q; rw [hf.absent] at h; contradiction
    simp [commit, hn, h]

/-- Same request identity is handled before CAS; this is a replay, not a second commit. -/
theorem immediate_idempotency {policy s r} (_h : FreshCommit policy s r) :
    applyRequest policy (commit s r) r = (commit s r, .replayed (resultGrant r)) :=
  exact_replay (fresh_receipt s r) rfl

theorem version_conflict {policy s r} (hn : s.receipts r.reqID = none)
    (hv : r.expected ≠ versions s r) :
    applyRequest policy s r = (s, .versionConflict) := by simp [applyRequest, hn, hv]

/-- Applies across different cases on this resource, including KEEP_LOCKED. An already
recorded request takes the replay/conflict branch instead of the VersionConflict branch. -/
theorem anti_race_mutual_exclusion {policy s r₁ r₂}
    (_h₁ : FreshCommit policy s r₁) (hn : s.receipts r₂.reqID = none)
    (hid : r₂.reqID ≠ r₁.reqID)
    (hv : r₂.expected.resourceVersion = s.resourceVersion) :
    applyRequest policy (commit s r₁) r₂ = (commit s r₁, .versionConflict) := by
  have hn' : (commit s r₁).receipts r₂.reqID = none := by simp [commit, hid, hn]
  apply version_conflict hn'
  intro he
  have he' := congrArg VersionPair.resourceVersion he
  simp only [versions, commit] at he'
  omega

theorem immutable_lineage_chain {policy s r a p pg g}
    (h : FreshCommit policy s r) (hd : r.decision = .authorizeNewAction a p pg g) :
    (applyRequest policy s r).1.lineage = ⟨r.reqID, a, p, pg, g⟩ :: s.lineage ∧
    (applyRequest policy s r).1.activeGrant = some g ∧
    (applyRequest policy s r).1.actuator = s.actuator := by
  rw [fresh_commit_accepted h]
  simp [commit, hd, resultGrant]

theorem lineage_preserved (policy : Request → Bool) (s : State) (r : Request)
    (entry : Lineage) (h : entry ∈ s.lineage) : entry ∈ (applyRequest policy s r).1.lineage := by
  rcases apply_cases policy s r with he | ⟨_, he⟩
  · rw [he]; exact h
  · rw [he]; cases hd : r.decision <;> simp [commit, hd, h]

inductive Run (policy : Request → Bool) : State → List Request → State → Prop where
  | nil {s} : Run policy s [] s
  | snoc {s t rs r} (h : Run policy s rs t) :
      Run policy s (rs ++ [r]) (applyRequest policy t r).1

theorem run_history_preservation {policy s t rs} (h : Run policy s rs t) :
    t.actuator = s.actuator := by
  induction h with
  | nil => rfl
  | snoc hr ih => rw [history_preservation, ih]

theorem run_receipt_preservation {policy s t rs} (h : Run policy s rs t)
    (q : Nat) (old : Receipt) (ho : s.receipts q = some old) : t.receipts q = some old := by
  induction h with
  | nil => exact ho
  | snoc hr ih => exact receipt_preservation _ _ _ _ _ ih

theorem run_used_grants_preserved {policy s t rs} (h : Run policy s rs t)
    (g : Nat) (hg : g ∈ s.usedGrants) : g ∈ t.usedGrants := by
  induction h with
  | nil => exact hg
  | snoc hr ih => exact used_grants_preserved _ _ _ _ ih

theorem run_lineage_preserved {policy s t rs} (h : Run policy s rs t)
    (entry : Lineage) (he : entry ∈ s.lineage) : entry ∈ t.lineage := by
  induction h with
  | nil => exact he
  | snoc hr ih => exact lineage_preserved _ _ _ _ ih

/-- A recorded decision can never become a second fresh acceptance, even after other cases. -/
theorem no_second_commit {policy s t rs r old g} (h : Run policy s rs t)
    (ho : s.receipts r.reqID = some old) :
    (applyRequest policy t r).2 ≠ .accepted g := by
  intro ha
  have hf := (accepted_iff.mp ha).1
  have hp := run_receipt_preservation h r.reqID old ho
  rw [hf.absent] at hp
  contradiction

theorem replay_after_interleaving {policy s t rs r} (h : Run policy (commit s r) rs t) :
    applyRequest policy t r = (t, .replayed (resultGrant r)) :=
  exact_replay (run_receipt_preservation h _ _ (fresh_receipt s r)) rfl

/-- Arbitration never restores the old actuator right; any intervening ordinary actuator
run is governed separately by the imported contract's spent-permit theorem. -/
theorem recovered_action_remains_disabled {policy t rs}
    (s : State) (a : Nat)
    (h : Run policy { s with actuator := ExternalActuatorContract.recover s.actuator } rs t) :
    t.actuator.permit a = false := by
  rw [run_history_preservation h]
  rfl

theorem inactive_old_grant_stays_inactive {policy s t rs g}
    (h : Run policy s rs t) (hu : g ∈ s.usedGrants)
    (hi : s.activeGrant ≠ some g) : t.activeGrant ≠ some g := by
  induction h with
  | nil => exact hi
  | snoc hr ih =>
    rcases apply_cases _ _ _ with he | ⟨hf, he⟩
    · rw [he]; exact ih
    · rw [he]
      exact no_old_grant_on_fresh_commit hf (run_used_grants_preserved hr g hu)

/-- Arbitration steps are stutters in the actuator projection; ordinary steps retain
all original authorization/confirmation requirements. This is not a grant adapter. -/
inductive CombinedRun (policy : Request → Bool) (auth conf : Nat → Prop) :
    State → List (ExternalActuatorContract.Event Nat) → State → Prop where
  | nil {s} : CombinedRun policy auth conf s [] s
  | arbitrate {s t events r} (h : CombinedRun policy auth conf s events t) :
      CombinedRun policy auth conf s events (applyRequest policy t r).1
  | actuator {s t events event next} (h : CombinedRun policy auth conf s events t)
      (hs : ExternalActuatorContract.Step auth conf t.actuator event next) :
      CombinedRun policy auth conf s (events ++ [event]) { t with actuator := next }

theorem combined_run_projection {policy auth conf s t events}
    (h : CombinedRun policy auth conf s events t) :
    ExternalActuatorContract.Run auth conf s.actuator events t.actuator := by
  induction h with
  | nil => exact .nil
  | arbitrate hr ih => rw [history_preservation]; exact ih
  | actuator hr hs ih => exact .snoc ih hs

theorem combined_at_most_one_dispatch {policy auth conf t events}
    (h : CombinedRun policy auth conf initial events t) (a : Nat) :
    ExternalActuatorContract.dispatchCount events a ≤ 1 :=
  ExternalActuatorContract.at_most_one_dispatch (combined_run_projection h) a

theorem combined_no_old_permit {policy auth conf s t events a}
    (h : CombinedRun policy auth conf s events t)
    (hj : s.actuator.journal a ≠ none) (hp : s.actuator.permit a = false) :
    t.actuator.permit a = false :=
  ExternalActuatorContract.run_preserves_spent (combined_run_projection h) a hj hp

/-- A thin reusable suite; the module's other results have stronger concrete statements. -/
structure ActuatorArbitrationContractSuite : Prop where
  history : ∀ policy s r, (applyRequest policy s r).1.actuator = s.actuator
  replay : ∀ policy s r, FreshCommit policy s r →
    applyRequest policy (commit s r) r = (commit s r, .replayed (resultGrant r))
  exclusion : ∀ policy s r₁ r₂, FreshCommit policy s r₁ → s.receipts r₂.reqID = none →
    r₂.reqID ≠ r₁.reqID → r₂.expected.resourceVersion = s.resourceVersion →
    applyRequest policy (commit s r₁) r₂ = (commit s r₁, .versionConflict)

theorem verification_suite : ActuatorArbitrationContractSuite :=
  ⟨history_preservation, fun _ _ _ h => immediate_idempotency h,
    fun _ _ _ _ h hn hi hv => anti_race_mutual_exclusion h hn hi hv⟩

end ActuatorArbitrationContract

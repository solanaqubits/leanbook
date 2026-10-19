/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

/-! A sequential abstract actuator model. A reserve transition represents a completed
trusted durable write, not a request to write. No cryptographic, physical, persistence,
fencing or implementation refinement claim is made. No transition erases history.
The event `issue` is one software command dispatch, not an electrical or mechanical effect.
-/
namespace ExternalActuatorContract
set_option backward.isDefEq.respectTransparency false

inductive LogStatus where
  | armed | executed | safetyLockout
  deriving DecidableEq, Repr

/-- Absence is `none` in the durable map, not an erasable last-action slot. -/
structure State (Action : Type*) where
  journal : Action → Option LogStatus
  permit : Action → Bool

inductive Event (Action : Type*) where
  | reserve (id : Action)
  | issue (id : Action)
  | recover
  | complete (id : Action)
  | lockout (id : Action)
  deriving DecidableEq, Repr

variable {Action : Type*} [DecidableEq Action]

def initial : State Action := ⟨fun _ => none, fun _ => false⟩

def reserve (s : State Action) (id : Action) : State Action :=
  ⟨fun a => if a = id then some .armed else s.journal a,
   fun a => if a = id then true else s.permit a⟩

def issue (s : State Action) (id : Action) : State Action :=
  ⟨s.journal, fun a => if a = id then false else s.permit a⟩

/-- Reads the same trusted durable map and drops every volatile permission. -/
def recover (s : State Action) : State Action := ⟨s.journal, fun _ => false⟩

def finish (s : State Action) (id : Action) (status : LogStatus) : State Action :=
  ⟨fun a => if a = id then some status else s.journal a,
   fun a => if a = id then false else s.permit a⟩

/-- Authority and action-bound confirmation are external predicates. This relation
encodes completed durable operations and exclusive serialization as model assumptions.
Recovered ARMED may remain ARMED until a durable lockout write completes; it has no permit. -/
inductive Step (authorized confirmed : Action → Prop) :
    State Action → Event Action → State Action → Prop where
  | reserve {s id} (h_authority : authorized id) (h_absent : s.journal id = none) :
      Step authorized confirmed s (.reserve id) (reserve s id)
  | issue {s id} (h_armed : s.journal id = some .armed) (h_permit : s.permit id = true) :
      Step authorized confirmed s (.issue id) (issue s id)
  | recover {s} : Step authorized confirmed s .recover (recover s)
  | complete {s id} (h_armed : s.journal id = some .armed)
      (h_spent : s.permit id = false) (h_confirmation : confirmed id) :
      Step authorized confirmed s (.complete id) (finish s id .executed)
  | lockout {s id} (h_present : s.journal id ≠ none) :
      Step authorized confirmed s (.lockout id) (finish s id .safetyLockout)

inductive Run (authorized confirmed : Action → Prop) :
    State Action → List (Event Action) → State Action → Prop where
  | nil {s} : Run authorized confirmed s [] s
  | snoc {s t u events event} (h_run : Run authorized confirmed s events t)
      (h_step : Step authorized confirmed t event u) :
      Run authorized confirmed s (events ++ [event]) u

def dispatchCount (events : List (Event Action)) (id : Action) : Nat :=
  events.count (.issue id)

def credit (s : State Action) (id : Action) : Nat := if s.permit id then 1 else 0

def occupied (s : State Action) (id : Action) : Nat :=
  if s.journal id = none then 0 else 1

def Budget (s : State Action) (id : Action) (count : Nat) : Prop :=
  count + credit s id ≤ occupied s id

omit [DecidableEq Action] in
@[simp] theorem recovered_has_no_permit (s : State Action) (id : Action) :
    (recover s).permit id = false := rfl

omit [DecidableEq Action] in
/-- Stronger than the requested armed-only implication. -/
theorem recovered_armed_no_permit (s : State Action) (id : Action)
    (_h : (recover s).journal id = some .armed) :
    (recover s).permit id = false := rfl

omit [DecidableEq Action] in
@[simp] theorem recovery_preserves_journal (s : State Action) :
    (recover s).journal = s.journal := rfl

theorem no_issue_after_recovery (authorized confirmed : Action → Prop)
    (s t : State Action) (id : Action) :
    ¬ Step authorized confirmed (recover s) (.issue id) t := by
  intro h
  cases h with
  | issue _ hp => simp [recover] at hp

theorem step_preserves_history {authorized confirmed : Action → Prop}
    {s t : State Action} {event : Event Action}
    (h : Step authorized confirmed s event t) (id : Action)
    (hp : s.journal id ≠ none) : t.journal id ≠ none := by
  cases h <;> simp_all [reserve, issue, recover, finish]
  all_goals split <;> simp_all

theorem step_preserves_budget {authorized confirmed : Action → Prop}
    {s t : State Action} {event : Event Action}
    (h : Step authorized confirmed s event t) (id : Action) (n : Nat)
    (hb : Budget s id n) :
    Budget t id (n + if event = .issue id then 1 else 0) := by
  cases h with
  | reserve ha hn =>
    rename_i a
    by_cases he : id = a
    · subst a; simp_all [Budget, credit, occupied, reserve]
    · simp_all [Budget, credit, occupied, reserve]
  | issue ha hp =>
    rename_i a
    by_cases he : id = a
    · subst a; simpa [Budget, credit, occupied, issue, ha, hp] using hb
    · simpa [Budget, credit, occupied, issue, he, Ne.symm he] using hb
  | recover =>
    have hn : n ≤ occupied s id := Nat.le_trans (Nat.le_add_right n (credit s id)) hb
    simpa [Budget, credit, occupied, recover] using hn
  | complete ha hp hc =>
    rename_i a
    by_cases he : id = a
    · subst a; simpa [Budget, credit, occupied, finish, ha, hp] using hb
    · simpa [Budget, credit, occupied, finish, he] using hb
  | lockout hp =>
    rename_i a
    by_cases he : id = a
    · subst a
      simp_all [Budget, credit, occupied, finish]
      split at hb <;> omega
    · simpa [Budget, credit, occupied, finish, he] using hb

theorem dispatchCount_snoc (events : List (Event Action)) (event : Event Action) (id : Action) :
    dispatchCount (events ++ [event]) id =
      dispatchCount events id + if event = .issue id then 1 else 0 := by
  by_cases he : event = .issue id
  · simp [dispatchCount, he]
  · simp [dispatchCount, he]

/-- The trace invariant is derived from Step, not postulated as a no-repeat premise. -/
theorem run_budget {authorized confirmed : Action → Prop}
    {events : List (Event Action)} {s : State Action}
    (h : Run authorized confirmed initial events s) (id : Action) :
    Budget s id (dispatchCount events id) := by
  generalize hi : initial = start at h
  induction h with
  | nil => subst start; simp [Budget, dispatchCount, initial, credit, occupied]
  | snoc hr hs ih =>
    have hb := step_preserves_budget hs id _ ih
    simpa only [dispatchCount_snoc] using hb

theorem at_most_one_dispatch {authorized confirmed : Action → Prop}
    {events : List (Event Action)} {s : State Action}
    (h : Run authorized confirmed initial events s) (id : Action) :
    dispatchCount events id ≤ 1 := by
  have hb := run_budget h id
  unfold Budget occupied at hb
  split at hb <;> omega

/-- Bound for any implementation trace with an explicit model-refinement witness.
This does not prove that a real driver, NV medium or controller supplies that witness. -/
theorem implementation_bound {Concrete : Type*} (observe : Concrete → List (Event Action))
    (authorized confirmed : Action → Prop) (execution : Concrete)
    (h_refinement : ∃ s, Run authorized confirmed initial (observe execution) s)
    (id : Action) : dispatchCount (observe execution) id ≤ 1 := by
  obtain ⟨s, hs⟩ := h_refinement
  exact at_most_one_dispatch hs id


theorem run_preserves_history {authorized confirmed : Action → Prop}
    {s t : State Action} {events : List (Event Action)}
    (h : Run authorized confirmed s events t) (id : Action)
    (hp : s.journal id ≠ none) : t.journal id ≠ none := by
  induction h with
  | nil => exact hp
  | snoc hr hs ih => exact step_preserves_history hs id ih

/-- A spent permission for an existing action can never be re-created. -/
theorem step_preserves_spent {authorized confirmed : Action → Prop}
    {s t : State Action} {event : Event Action}
    (h : Step authorized confirmed s event t) (id : Action)
    (hj : s.journal id ≠ none) (hp : s.permit id = false) : t.permit id = false := by
  cases h with
  | reserve ha hn =>
    rename_i a
    by_cases he : id = a
    · subst a; exact False.elim (hj hn)
    · simp [reserve, he, hp]
  | issue => simp [issue, hp]
  | recover => rfl
  | complete => simp [finish, hp]
  | lockout => simp [finish, hp]

theorem run_preserves_spent {authorized confirmed : Action → Prop}
    {s t : State Action} {events : List (Event Action)}
    (h : Run authorized confirmed s events t) (id : Action)
    (hj : s.journal id ≠ none) (hp : s.permit id = false) : t.permit id = false := by
  induction h with
  | nil => exact hp
  | snoc hr hs ih =>
    exact step_preserves_spent hs id (run_preserves_history hr id hj) ih

/-- Recovery cannot be followed by eventual re-authorization of an old action,
even if other actions are processed before the attempted replay. -/
theorem recovered_action_stays_disabled {authorized confirmed : Action → Prop}
    (s t : State Action) (id : Action) {events : List (Event Action)}
    (hj : s.journal id ≠ none)
    (h : Run authorized confirmed (recover s) events t) : t.permit id = false :=
  run_preserves_spent h id hj rfl

def preCrashEvents (id : Action) : List (Event Action) := [.reserve id, .recover]
def postCrashEvents (id : Action) : List (Event Action) := [.reserve id, .issue id, .recover]
def preCrashState (id : Action) : State Action := recover (reserve initial id)
def postCrashState (id : Action) : State Action := recover (issue (reserve initial id) id)

theorem pre_crash_reachable (authorized confirmed : Action → Prop) (id : Action)
    (ha : authorized id) :
    Run authorized confirmed initial (preCrashEvents id) (preCrashState id) :=
  .snoc (.snoc .nil (.reserve ha rfl)) .recover

theorem post_crash_reachable (authorized confirmed : Action → Prop) (id : Action)
    (ha : authorized id) :
    Run authorized confirmed initial (postCrashEvents id) (postCrashState id) := by
  exact .snoc (.snoc (.snoc .nil (.reserve ha rfl)) (.issue (by simp [reserve])
    (by simp [reserve]))) .recover

/-- Even the full recovered controller state is identical, not only one selected entry. -/
theorem recovered_states_equal (id : Action) : preCrashState id = postCrashState id := rfl

def observe {Sensor : Type*} (s : State Action) (sensor : Sensor) :
    (Action → Option LogStatus) × Sensor := (s.journal, sensor)

theorem indistinguishable_crashes {Sensor : Type*} (id : Action) (sensor : Sensor) :
    observe (preCrashState id) sensor = observe (postCrashState id) sensor := rfl

@[simp] theorem pre_crash_dispatch_count (id : Action) :
    dispatchCount (preCrashEvents id) id = 0 := by simp [dispatchCount, preCrashEvents]

@[simp] theorem post_crash_dispatch_count (id : Action) :
    dispatchCount (postCrashEvents id) id = 1 := by simp [dispatchCount, postCrashEvents]

/-- No deterministic classifier using only this observation correctly classifies both
valid histories. Equal sensor readings are an explicit premise, not a sensor physics theorem. -/
theorem no_observation_classifier {Sensor : Type*}
    (id : Action) (sensor : Sensor)
    (classify : ((Action → Option LogStatus) × Sensor) → Bool) :
    ¬ (classify (observe (preCrashState id) sensor) = false ∧
       classify (observe (postCrashState id) sensor) = true) := by
  rw [indistinguishable_crashes id sensor]
  intro h
  exact Bool.false_ne_true (h.1.symm.trans h.2)

/-- Concrete reachable counterexamples support the classifier impossibility result. -/
theorem reachable_indistinguishable_histories {Sensor : Type*}
    (authorized confirmed : Action → Prop) (id : Action) (sensor : Sensor)
    (ha : authorized id) :
    Run authorized confirmed initial (preCrashEvents id) (preCrashState id) ∧
    Run authorized confirmed initial (postCrashEvents id) (postCrashState id) ∧
    observe (preCrashState id) sensor = observe (postCrashState id) sensor ∧
    dispatchCount (preCrashEvents id) id = 0 ∧ dispatchCount (postCrashEvents id) id = 1 :=
  ⟨pre_crash_reachable _ _ _ ha, post_crash_reachable _ _ _ ha,
   indistinguishable_crashes _ _, pre_crash_dispatch_count _, post_crash_dispatch_count _⟩

/-- Selected guarantees over arbitrary small action types; implementations need an
independent refinement argument. No hash, grant signature, sensor or hardware axiom. -/
structure ExternalActuatorContractSuite : Prop where
  recovery : ∀ (A : Type) (s : State A) (id : A), (recover s).permit id = false
  trace_bound : ∀ (A : Type) [DecidableEq A] (auth conf : A → Prop)
    (events : List (Event A)) (s : State A), Run auth conf initial events s →
    ∀ id, dispatchCount events id ≤ 1
  ambiguity : ∀ (A : Type) [DecidableEq A] (id : A) (v : Bool),
    observe (preCrashState id) v = observe (postCrashState id) v

theorem verification_suite : ExternalActuatorContractSuite :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ h id => at_most_one_dispatch h id,
   fun _ _ _ _ => rfl⟩

end ExternalActuatorContract

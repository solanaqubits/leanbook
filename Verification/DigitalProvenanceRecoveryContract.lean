/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DigitalProvenanceReplayContract

/-! Pure sequential persistence model. Completed writes and an independent trusted
prefix survive crashes by the transition semantics, not by a claim about hardware.
No filesystem, concurrent writer, hash commitment or exactly-once delivery. -/
namespace DigitalProvenanceRecoveryContract
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract
open DigitalProvenanceReplayContract

/-- Chronological completed entries; base may contain duplicate consumed bytes. -/
structure RegistryImage where
  base : ChallengeRegistry
  entries : List ByteArray
  deriving DecidableEq

/-- Independent trusted content, not a sequence number stored in the same image. -/
structure TrustedPrefix where
  base : ChallengeRegistry
  entries : List ByteArray
  deriving DecidableEq

def registryAt (base : ChallengeRegistry) (entries : List ByteArray) : ChallengeRegistry :=
  ⟨base.context, entries.reverse ++ base.usedChallenges⟩

@[simp] theorem registryAt_context (b es) : (registryAt b es).context = b.context := rfl

@[simp] theorem mem_registryAt (b es c) :
    c ∈ (registryAt b es).usedChallenges ↔ c ∈ es ∨ c ∈ b.usedChallenges := by
  simp [registryAt]

theorem registryAt_append (b es c) :
    registryAt b (es ++ [c]) =
      { registryAt b es with usedChallenges := c :: (registryAt b es).usedChallenges } := by
  simp [registryAt, List.reverse_append]

def ImageAccepted (expected : RegistryContext) (a : TrustedPrefix) (i : RegistryImage) : Prop :=
  a.base.context = expected ∧ i.base = a.base ∧ a.entries <+: i.entries

instance (e : RegistryContext) (a : TrustedPrefix) (i : RegistryImage) :
    Decidable (ImageAccepted e a i) := by
  unfold ImageAccepted
  infer_instance

/-- Membership safety only; an arbitrary suffix is not authenticated by this check. -/
def restoreRegistry? (expected : RegistryContext) (a : TrustedPrefix)
    (i : RegistryImage) : Option ChallengeRegistry :=
  if ImageAccepted expected a i then some (registryAt i.base i.entries) else none

theorem restore_iff (e a i r) : restoreRegistry? e a i = some r ↔
    ImageAccepted e a i ∧ registryAt i.base i.entries = r := by
  by_cases h : ImageAccepted e a i <;> simp [restoreRegistry?, h]

theorem restore_protected (e a i r) (h : restoreRegistry? e a i = some r) :
    (registryAt a.base a.entries).usedChallenges ⊆ r.usedChallenges := by
  rcases (restore_iff e a i r).mp h with ⟨⟨_, hb, hp⟩, rfl⟩
  intro c hc
  rw [mem_registryAt] at hc ⊢
  rcases hc with hc | hc
  · exact Or.inl (hp.subset hc)
  · exact Or.inr (by simpa [hb] using hc)

theorem restore_context (e a i r) (h : restoreRegistry? e a i = some r) :
    r.context = e := by
  rcases (restore_iff e a i r).mp h with ⟨⟨he, hb, _⟩, rfl⟩
  simpa [hb] using he

inductive Phase where
  | idle | prepared | durable | anchored
  deriving DecidableEq

/-- acknowledged is ghost history in this model; it is never decoded from an image. -/
structure State where
  committed : List ByteArray
  anchor : List ByteArray
  pending : Option ByteArray
  phase : Phase
  online : Bool
  acknowledged : List ByteArray
  deriving DecidableEq

def initial (b : ChallengeRegistry) : State :=
  ⟨[], [], none, .idle, true, b.usedChallenges⟩

def trusted (b : ChallengeRegistry) (s : State) : TrustedPrefix := ⟨b, s.anchor⟩

def image (b : ChallengeRegistry) (s : State) : RegistryImage := ⟨b, s.committed⟩

structure Result where
  state : State
  emitted : Option ByteArray
  authorization : AuthorizationStatus
  deriving DecidableEq

def quiet (s : State) : Result := ⟨s, none, .blocked⟩

def prepare (b : ChallengeRegistry) (s : State) (q : RedemptionRequest) : Result :=
  if s.online = true ∧ s.phase = .idle then
    match (redeemChallenge (registryAt b s.committed) q).report with
    | none => quiet s
    | some _ => quiet { s with pending := some q.expected.challenge, phase := .prepared }
  else quiet s

/-- This event is completion of a durable append, not invocation of write/fsync. -/
def persist (s : State) : Result :=
  if s.online = true ∧ s.phase = .prepared then
    match s.pending with
    | none => quiet s
    | some c => quiet { s with committed := s.committed ++ [c], phase := .durable }
  else quiet s

/-- A separate completed operation on the independent trusted content anchor. -/
def anchorCommit (s : State) : Result :=
  if s.online = true ∧ s.phase = .durable then
    quiet { s with anchor := s.committed, phase := .anchored }
  else quiet s

/-- External acceptance requires the bytes to be in the sealed durable prefix. -/
def acknowledge (s : State) : Result :=
  if s.online = true ∧ s.phase = .anchored then
    match s.pending with
    | none => quiet s
    | some c =>
      if c ∈ s.anchor then
        ⟨{ s with pending := none, phase := .idle, acknowledged := c :: s.acknowledged },
          some c, .blocked⟩
      else quiet s
  else quiet s

/-- Incomplete writes have no completion event. A completion immediately followed
by crash models a write whose completion the caller did not observe. -/
def crash (s : State) : Result :=
  quiet { s with pending := none, phase := .idle, online := false }

/-- Admissibility is exact retention of completed data, independently of ack history.
It permits either crash or persist-then-crash for a previously prepared write. -/
def AdmissibleCrashImage (b : ChallengeRegistry) (s : State) (i : RegistryImage) : Prop :=
  i = image b s

/-- The service model resumes only its completed journal. Arbitrary external image
safety is stated separately for restoreRegistry?, not as provenance of a suffix. -/
def recover (b : ChallengeRegistry) (expected : RegistryContext) (s : State)
    (i : RegistryImage) : Result :=
  if s.online = false ∧ i = image b s then
    match restoreRegistry? expected (trusted b s) i with
    | none => quiet s
    | some _ => quiet { s with pending := none, phase := .idle, online := true }
  else quiet s

inductive Action where
  | prepare (request : RedemptionRequest)
  | persist | anchorCommit | acknowledge | crash
  | recover (expected : RegistryContext) (candidate : RegistryImage)

def step (b : ChallengeRegistry) (s : State) : Action → Result
  | .prepare q => prepare b s q
  | .persist => persist s
  | .anchorCommit => anchorCommit s
  | .acknowledge => acknowledge s
  | .crash => crash s
  | .recover e i => recover b e s i

def run (b : ChallengeRegistry) (s : State) : List Action → State
  | [] => s
  | a :: as => run b (step b s a).state as

/-- The invariant is proved from initial/step, not required as a recovery input. -/
def Invariant (b : ChallengeRegistry) (s : State) : Prop :=
  s.anchor <+: s.committed ∧
    s.acknowledged ⊆ (registryAt b s.anchor).usedChallenges

theorem initial_invariant (b) : Invariant b (initial b) := by
  simp [Invariant, initial, registryAt]

theorem prepare_invariant (b s q) (h : Invariant b s) :
    Invariant b (prepare b s q).state := by
  unfold prepare
  split
  · split <;> exact h
  · exact h

theorem persist_invariant (b s) (h : Invariant b s) :
    Invariant b (persist s).state := by
  unfold persist
  split
  · split
    · exact h
    · exact ⟨List.prefix_append_of_prefix h.1, h.2⟩
  · exact h

theorem seal_invariant (b s) (h : Invariant b s) :
    Invariant b (anchorCommit s).state := by
  unfold anchorCommit
  split
  · refine ⟨List.prefix_refl _, ?_⟩
    intro c hc
    have hm := h.2 hc
    rw [mem_registryAt] at hm ⊢
    exact hm.elim (fun hm => Or.inl (h.1.subset hm)) Or.inr
  · exact h

theorem acknowledge_invariant (b s) (h : Invariant b s) :
    Invariant b (acknowledge s).state := by
  unfold acknowledge
  split
  · split
    · exact h
    · split
      · rename_i c _ hc
        refine ⟨h.1, ?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact (mem_registryAt b s.anchor _).mpr (Or.inl hc)
        · exact h.2 hd
      · exact h
  · exact h

theorem crash_invariant (b s) (h : Invariant b s) :
    Invariant b (crash s).state := h

theorem recover_invariant (b e s i) (h : Invariant b s) :
    Invariant b (recover b e s i).state := by
  unfold recover
  split
  · split <;> exact h
  · exact h

theorem step_invariant (b s a) (h : Invariant b s) :
    Invariant b (step b s a).state := by
  cases a with
  | prepare q => exact prepare_invariant b s q h
  | persist => exact persist_invariant b s h
  | anchorCommit => exact seal_invariant b s h
  | acknowledge => exact acknowledge_invariant b s h
  | crash => exact crash_invariant b s h
  | recover e i => exact recover_invariant b e s i h

theorem run_invariant (b s as) (h : Invariant b s) : Invariant b (run b s as) := by
  induction as generalizing s with
  | nil => exact h
  | cons a as ih => exact ih _ (step_invariant b s a h)

def Reachable (b : ChallengeRegistry) (s : State) : Prop :=
  ∃ actions, run b (initial b) actions = s

theorem reachable_invariant (b s) (h : Reachable b s) : Invariant b s := by
  obtain ⟨as, rfl⟩ := h
  exact run_invariant b _ as (initial_invariant b)

/-- Main recovery theorem: arbitrary accepted image, but the actual trusted anchor
and acknowledged history are taken from a reachable state. -/
theorem crash_recovery_sound (b s e i r) (hr : Reachable b s)
    (hv : restoreRegistry? e (trusted b s) i = some r) :
    s.acknowledged ⊆ r.usedChallenges := by
  intro c hc
  exact restore_protected e (trusted b s) i r hv ((reachable_invariant b s hr).2 hc)

theorem recovered_replay_rejected (b s e i r q) (hr : Reachable b s)
    (hv : restoreRegistry? e (trusted b s) i = some r)
    (hc : q.expected.challenge ∈ s.acknowledged) : redeemChallenge r q = reject r :=
  used_challenge_rejected r q (crash_recovery_sound b s e i r hr hv hc)

/-- Exact restoration of the retained completed journal, with no ghost history input. -/
theorem admissible_restore (b s i) (hr : Reachable b s)
    (hi : AdmissibleCrashImage b s i) :
    restoreRegistry? b.context (trusted b s) i = some (registryAt b s.committed) := by
  subst i
  apply (restore_iff _ _ _ _).mpr
  exact ⟨⟨rfl, rfl, (reachable_invariant b s hr).1⟩, rfl⟩

theorem prepare_failure_unchanged (b s q)
    (hf : (redeemChallenge (registryAt b s.committed) q).report = none) :
    prepare b s q = quiet s := by
  simp [prepare, hf]

theorem recover_failure_unchanged (b e s i)
    (hf : restoreRegistry? e (trusted b s) i = none) : recover b e s i = quiet s := by
  simp [recover, hf]

theorem crash_preserves (s) :
    (crash s).state.committed = s.committed ∧ (crash s).state.anchor = s.anchor ∧
      (crash s).state.acknowledged = s.acknowledged ∧ (crash s).state.online = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem result_blocked (r : Result) : r.authorization = .blocked := by
  cases r.authorization
  rfl

/-- Only acknowledge emits an external acceptance, with its exact ghost update. -/
theorem emitted_records (b s a c) (he : (step b s a).emitted = some c) :
    (step b s a).state.acknowledged = c :: s.acknowledged ∧ c ∈ s.anchor := by
  cases a with
  | prepare q =>
    simp only [step] at he
    unfold prepare at he
    split at he
    · split at he <;> simp [quiet] at he
    · simp [quiet] at he
  | persist =>
    simp only [step] at he
    unfold persist at he
    split at he
    · split at he <;> simp [quiet] at he
    · simp [quiet] at he
  | anchorCommit =>
    simp only [step] at he
    unfold anchorCommit at he
    split at he <;> simp [quiet] at he
  | acknowledge =>
    simp only [step] at he ⊢
    unfold acknowledge at he ⊢
    split at he <;> rename_i hg
    · rw [if_pos hg]
      split at he <;> rename_i hp
      · simp [quiet] at he
      · split at he <;> rename_i hm
        · simp only [Option.some.injEq] at he
          subst c
          simp [hm]
        · simp [quiet] at he
    · simp [quiet] at he
  | crash => simp [step, crash, quiet] at he
  | recover e i =>
    simp only [step] at he
    unfold recover at he
    split at he
    · split at he <;> simp [quiet] at he
    · simp [quiet] at he

theorem step_monotone (b s a) (h : Invariant b s) :
    s.anchor <+: (step b s a).state.anchor ∧
    s.committed <+: (step b s a).state.committed ∧
    s.acknowledged ⊆ (step b s a).state.acknowledged := by
  cases a with
  | prepare q =>
    simp only [step]
    unfold prepare
    split
    · split <;> simp [quiet]
    · simp [quiet]
  | persist =>
    simp only [step]
    unfold persist
    split
    · split <;> simp [quiet]
    · simp [quiet]
  | anchorCommit =>
    simp only [step]
    unfold anchorCommit
    split
    · simpa [quiet] using h.1
    · simp [quiet]
  | acknowledge =>
    simp only [step]
    unfold acknowledge
    split
    · split
      · simp [quiet]
      · split
        · exact ⟨List.prefix_rfl, List.prefix_rfl, fun _ hm => List.mem_cons_of_mem _ hm⟩
        · simp [quiet]
    · simp [quiet]
  | crash => simp [step, crash, quiet]
  | recover e i =>
    simp only [step]
    unfold recover
    split
    · split <;> simp [quiet]
    · simp [quiet]

theorem run_monotone (b s as) (h : Invariant b s) :
    s.anchor <+: (run b s as).anchor ∧ s.committed <+: (run b s as).committed ∧
      s.acknowledged ⊆ (run b s as).acknowledged := by
  induction as generalizing s with
  | nil => exact ⟨List.prefix_rfl, List.prefix_rfl, List.Subset.refl _⟩
  | cons a as ih =>
    have hs := step_monotone b s a h
    have ht := ih (step b s a).state (step_invariant b s a h)
    exact ⟨hs.1.trans ht.1, hs.2.1.trans ht.2.1, fun _ hc => ht.2.2 (hs.2.2 hc)⟩

theorem run_append (b s xs ys) : run b s (xs ++ ys) = run b (run b s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem reachable_run (b s xs) (h : Reachable b s) : Reachable b (run b s xs) := by
  obtain ⟨ys, rfl⟩ := h
  exact ⟨ys ++ xs, run_append b _ ys xs⟩

theorem reachable_step (b s a) (h : Reachable b s) : Reachable b (step b s a).state :=
  reachable_run b s [a] h

/-- A real emitted acceptance remains consumed after an arbitrary legal tail and recovery. -/
theorem emitted_replay_after_recovery (b s a c tail e i r q)
    (hr : Reachable b s) (he : (step b s a).emitted = some c)
    (hv : restoreRegistry? e (trusted b (run b (step b s a).state tail)) i = some r)
    (hc : q.expected.challenge = c) : redeemChallenge r q = reject r := by
  have hs := reachable_step b s a hr
  have ht := reachable_run b (step b s a).state tail hs
  apply recovered_replay_rejected b _ e i r q ht hv
  rw [hc]
  apply (run_monotone b _ tail (reachable_invariant b _ hs)).2.2
  rw [(emitted_records b s a c he).1]
  exact List.mem_cons_self

theorem recover_admissible_online (b s i) (hr : Reachable b s)
    (ho : s.online = false) (hi : AdmissibleCrashImage b s i) :
    (recover b b.context s i).state.online = true := by
  have hv := admissible_restore b s i hr hi
  rw [recover, if_pos ⟨ho, hi⟩, hv]
  rfl

theorem emitted_is_durable (b s a c) (hr : Reachable b s)
    (he : (step b s a).emitted = some c) : c ∈ s.committed :=
  (reachable_invariant b s hr).1.subset (emitted_records b s a c he).2

theorem prepare_success (b s q report) (ho : s.online = true) (hp : s.phase = .idle)
    (hv : (redeemChallenge (registryAt b s.committed) q).report = some report) :
    prepare b s q = quiet { s with pending := some q.expected.challenge, phase := .prepared } := by
  simp [prepare, ho, hp, hv]

/-- The completed append implements exactly the consumed-list update of epsilon255. -/
theorem persist_refines_redemption (b s q report) (ho : s.online = true)
    (hp : s.phase = .idle)
    (hv : (redeemChallenge (registryAt b s.committed) q).report = some report) :
    registryAt b (persist (prepare b s q).state).state.committed =
      (redeemChallenge (registryAt b s.committed) q).registry := by
  rw [prepare_success b s q report ho hp hv]
  simp only [quiet, persist, ho, and_self, if_true]
  rw [registryAt_append, accepted_registry _ q report hv]

theorem refusal_stays_offline (b e s i) (ho : s.online = false)
    (hf : restoreRegistry? e (trusted b s) i = none) :
    (recover b e s i).state.online = false := by
  rw [recover_failure_unchanged b e s i hf]
  exact ho

structure ProvenanceRecoverySuite : Prop where
  restore_exact : ∀ e a i r, restoreRegistry? e a i = some r ↔
    ImageAccepted e a i ∧ registryAt i.base i.entries = r
  invariant : ∀ b s, Reachable b s → Invariant b s
  no_ack_loss : ∀ b s e i r, Reachable b s →
    restoreRegistry? e (trusted b s) i = some r → s.acknowledged ⊆ r.usedChallenges
  complete : ∀ b s i, Reachable b s → AdmissibleCrashImage b s i →
    restoreRegistry? b.context (trusted b s) i = some (registryAt b s.committed)
  context : ∀ e a i r, restoreRegistry? e a i = some r → r.context = e
  emitted_replay : ∀ b s a c tail e i r q, Reachable b s →
    (step b s a).emitted = some c →
    restoreRegistry? e (trusted b (run b (step b s a).state tail)) i = some r →
    q.expected.challenge = c → redeemChallenge r q = reject r
  emitted_durable : ∀ b s a c, Reachable b s →
    (step b s a).emitted = some c → c ∈ s.committed
  monotone : ∀ b s xs, Invariant b s →
    s.anchor <+: (run b s xs).anchor ∧ s.committed <+: (run b s xs).committed ∧
    s.acknowledged ⊆ (run b s xs).acknowledged
  refusal : ∀ b s q, (redeemChallenge (registryAt b s.committed) q).report = none →
    prepare b s q = quiet s
  blocked : ∀ r : Result, r.authorization = .blocked

theorem verification_suite : ProvenanceRecoverySuite :=
  ⟨restore_iff, reachable_invariant, crash_recovery_sound, admissible_restore,
    restore_context, emitted_replay_after_recovery, emitted_is_durable, run_monotone,
    prepare_failure_unchanged, result_blocked⟩

end DigitalProvenanceRecoveryContract

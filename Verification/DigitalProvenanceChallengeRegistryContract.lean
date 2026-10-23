/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DigitalProvenanceReportContract

/-! Pure atomic transition model, not a database or a proof of runtime linearizability.
Versions are installed once. Outcomes survive response loss by model semantics.
No registry rollback, deletion, physical clocks or cryptographic security theorem. -/
namespace DigitalProvenanceChallengeRegistryContract
open DigitalProvenanceManifestContract DigitalProvenanceReportContract

structure Scope where
  contextId : String
  sessionId : String
  policyVersion : String
  deriving DecidableEq
structure ChallengeKey where
  scope : Scope
  challenge : ByteArray
  deriving DecidableEq
abbrev TransactionId := String
structure ContextConfig where
  expected : ExpectedContext
  limits : VerificationLimits
  allowMissingTimestamp : Bool

def scopeOf (c : ExpectedContext) : Scope :=
  ⟨c.contextId, c.expectedSessionId, c.expectedPolicyVersion⟩
def keyOf (c : ExpectedContext) : Option ChallengeKey :=
  c.activeChallenge.map (fun b => ⟨scopeOf c, b⟩)
structure Request where
  key : ChallengeKey
  contextVersion : String
  signed : SignedProvenanceV1
  snapshot : ByteArray
  profile : ByteArray
structure Binding where
  key : ChallengeKey
  message : ByteArray
  deriving DecidableEq
def bindingOf (q : Request) : Binding := ⟨q.key, signingMessageV1 q.signed.manifest⟩
structure ConsumedRecord where
  payloadDigest : Digest256
  pinnedContextVersion : String
  historicalReport : VerificationReport
  deriving DecidableEq
inductive EntryState where
  | issued
  | consumed (record : ConsumedRecord)
  deriving DecidableEq
inductive RedemptionFailure where
  | challenge_already_used | challenge_not_issued | verification_rejected | context_changed
  | transaction_conflict | transaction_not_started | transaction_aborted
  deriving DecidableEq
inductive AcceptanceKind where
  | newAcceptance | historicalReturn
  deriving DecidableEq
inductive RedemptionResult where
  | newly_consumed (record : ConsumedRecord)
  | idempotent_replay_matched (record : ConsumedRecord)
  | rejected (reason : RedemptionFailure)
  | indeterminate_transaction_state
  deriving DecidableEq
inductive TransactionState where
  | pending (binding : Binding)
  | committed (binding : Binding) (record : ConsumedRecord) (kind : AcceptanceKind)
  | aborted (binding : Binding) (reason : RedemptionFailure)
  deriving DecidableEq
inductive ResolutionResult where
  | confirmed_committed (record : ConsumedRecord) (kind : AcceptanceKind)
  | confirmed_not_committed
  | still_indeterminate
  deriving DecidableEq
structure State where
  entries : ChallengeKey → Option EntryState
  transactions : TransactionId → Option TransactionState
  contexts : String → Option ContextConfig
  active : Scope → Option String
  /-- Ghost log of new acceptance events, not a persistence implementation. -/
  accepted : List ChallengeKey

def initial : State := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => none, []⟩
def put {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) : α → β :=
  fun x => if x = k then v else f x
@[simp] theorem put_same {α β} [DecidableEq α] (f : α → β) k v : put f k v k = v := by simp [put]
@[simp] theorem put_other {α β} [DecidableEq α] (f : α → β) k v x (h : x ≠ k) :
    put f k v x = f x := by simp [put, h]

def reportAccepted (allow : Bool) (r : VerificationReport) : Bool :=
  decide (r.signature = .valid ∧ r.keyAuthorization = .authorized ∧
    r.contextBinding = .matched ∧ r.replay = .challenge_matched ∧
    r.snapshotBinding = .matched ∧ r.profileBinding = .matched ∧
    (r.freshness = .within_trusted_window ∨ (allow = true ∧ r.freshness = .no_timestamp)))

/-- Actual epsilon258 evaluation, never a caller-supplied positive report. -/
def checkNew (crypto : CryptoBackend) (cfg : ContextConfig) (q : Request) :
    Option ConsumedRecord := do
  if keyOf cfg.expected ≠ some q.key then none else do
    let r ← (verifyProvenance crypto cfg.limits cfg.expected q.signed q.snapshot q.profile).toOption
    if !reportAccepted cfg.allowMissingTimestamp r then none else do
      let d ← (crypto.sha256 (bindingOf q).message).toOption
      pure ⟨d, q.contextVersion, r⟩

/-- Historical return rechecks bounded bytes and bindings, not current key/time policy. -/
def retryValid (crypto : CryptoBackend) (cfg : ContextConfig) (q : Request)
    (r : ConsumedRecord) : Bool :=
  decide (InputsFit cfg.limits cfg.expected q.signed q.snapshot q.profile) &&
  decide (crypto.sha256 (bindingOf q).message = .ok r.payloadDigest) &&
  decide (q.snapshot.size = q.signed.manifest.snapshot.sizeBytes) &&
  decide (crypto.sha256 q.snapshot = .ok q.signed.manifest.snapshot.digest) &&
  decide (q.profile.size = q.signed.manifest.profile.sizeBytes) &&
  decide (crypto.sha256 q.profile = .ok q.signed.manifest.profile.digest)

def retry (crypto : CryptoBackend) (s : State) (q : Request) (r : ConsumedRecord) :
    RedemptionResult :=
  match s.contexts r.pinnedContextVersion with
  | none => .rejected .verification_rejected
  | some cfg =>
    if retryValid crypto cfg q r then .idempotent_replay_matched r
    else .rejected .verification_rejected

def decision (crypto : CryptoBackend) (s : State) (q : Request) : RedemptionResult :=
  match s.entries q.key with
  | none => .rejected .challenge_not_issued
  | some (.consumed r) =>
    if crypto.sha256 (bindingOf q).message = .ok r.payloadDigest then retry crypto s q r
    else .rejected .challenge_already_used
  | some .issued =>
    if s.active q.key.scope ≠ some q.contextVersion then .rejected .context_changed
    else match s.contexts q.contextVersion with
    | none => .rejected .context_changed
    | some cfg => match checkNew crypto cfg q with
      | none => .rejected .verification_rejected
      | some r => .newly_consumed r

def finish (s : State) (tx : TransactionId) (b : Binding) (result : RedemptionResult) : State :=
  match result with
  | .newly_consumed r =>
    { s with entries := put s.entries b.key (some (.consumed r))
             transactions := put s.transactions tx (some (.committed b r .newAcceptance))
             accepted := b.key :: s.accepted }
  | .idempotent_replay_matched r =>
    { s with transactions := put s.transactions tx (some (.committed b r .historicalReturn)) }
  | .rejected e => { s with transactions := put s.transactions tx (some (.aborted b e)) }
  | .indeterminate_transaction_state => s

def commitChecked (crypto : CryptoBackend) (s : State) (tx : TransactionId) (q : Request) :
    State × RedemptionResult :=
  match s.transactions tx with
  | none => (s, .rejected .transaction_not_started)
  | some (.pending b) =>
    if b ≠ bindingOf q then (s, .rejected .transaction_conflict)
    else let r := decision crypto s q; (finish s tx b r, r)
  | some (.aborted b e) =>
    (s, .rejected (if b = bindingOf q then e else .transaction_conflict))
  | some (.committed b r _) =>
    if b ≠ bindingOf q then (s, .rejected .transaction_conflict)
    else (s, retry crypto s q r)

def resolve (s : State) (key : ChallengeKey) (tx : TransactionId) : ResolutionResult :=
  match s.transactions tx with
  | some (.committed b r kind) =>
    if b.key = key then .confirmed_committed r kind else .still_indeterminate
  | some (.aborted b _) =>
    if b.key = key then .confirmed_not_committed else .still_indeterminate
  | _ => .still_indeterminate

inductive Input where
  | installContext (version : String) (cfg : ContextConfig)
  | issue (key : ChallengeKey)
  | beginTransaction (tx : TransactionId) (q : Request)
  | commit (tx : TransactionId) (q : Request)
  | abort (tx : TransactionId)
  | lookup (key : ChallengeKey)
  | resolveTransaction (key : ChallengeKey) (tx : TransactionId)
inductive Output where
  | administrative (accepted : Bool)
  | redemption (result : RedemptionResult)
  | entry (value : Option EntryState)
  | resolution (result : ResolutionResult)
  deriving DecidableEq

def step (crypto : CryptoBackend) (s : State) (i : Input) : State × Output :=
  match i with
  | .installContext v cfg =>
    if (s.contexts v).isSome then (s, .administrative false)
    else ({ s with contexts := put s.contexts v (some cfg)
                   active := put s.active (scopeOf cfg.expected) (some v) }, .administrative true)
  | .issue k =>
    if (s.entries k).isSome then (s, .administrative false)
    else match s.active k.scope >>= s.contexts with
      | none => (s, .administrative false)
      | some cfg =>
        if keyOf cfg.expected = some k then
          ({ s with entries := put s.entries k (some .issued) }, .administrative true)
        else (s, .administrative false)
  | .beginTransaction tx q =>
    if (s.transactions tx).isSome then (s, .administrative false)
    else ({ s with transactions := put s.transactions tx (some (.pending (bindingOf q))) },
      .administrative true)
  | .commit tx q => let r := commitChecked crypto s tx q; (r.1, .redemption r.2)
  | .abort tx => match s.transactions tx with
    | some (.pending b) =>
      ({ s with transactions := put s.transactions tx (some (.aborted b .transaction_aborted)) },
        .administrative true)
    | _ => (s, .administrative false)
  | .lookup k => (s, .entry (s.entries k))
  | .resolveTransaction k tx => (s, .resolution (resolve s k tx))

/-- Response loss changes observation only; a committed state is not rolled back. -/
def delivered (lost : Bool) (output : Output) : Option Output := if lost then none else some output

def run (crypto : CryptoBackend) : State → List Input → State
  | s, [] => s
  | s, i :: is => run crypto (step crypto s i).1 is

/-! Local decision facts, used to derive invariants rather than assume safety. -/
theorem retry_cases (crypto s q r) : retry crypto s q r = .rejected .verification_rejected ∨
    (∃ cfg, s.contexts r.pinnedContextVersion = some cfg ∧
      retryValid crypto cfg q r = true ∧ retry crypto s q r = .idempotent_replay_matched r) := by
  unfold retry
  split <;> simp_all

theorem retry_not_new (crypto s q r r') : retry crypto s q r ≠ .newly_consumed r' := by
  rcases retry_cases crypto s q r with h | ⟨cfg, hc, hv, h⟩ <;> simp [h]

theorem decision_new (crypto s q r) (h : decision crypto s q = .newly_consumed r) :
    s.entries q.key = some .issued ∧ s.active q.key.scope = some q.contextVersion ∧
    ∃ cfg, s.contexts q.contextVersion = some cfg ∧ checkNew crypto cfg q = some r := by
  unfold decision at h
  split at h
  · contradiction
  · split at h
    · exact False.elim (retry_not_new _ _ _ _ _ h)
    · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h <;> simp_all

theorem decision_retry (crypto s q r) (h : decision crypto s q = .idempotent_replay_matched r) :
    s.entries q.key = some (.consumed r) ∧
    ∃ cfg, s.contexts r.pinnedContextVersion = some cfg ∧ retryValid crypto cfg q r = true := by
  unfold decision at h
  split at h
  · contradiction
  · split at h
    · rename_i r₀ he hd
      rcases retry_cases crypto s q r₀ with hr | ⟨cfg, hc, hv, hr⟩
      · simp [hr] at h
      · simp only [hr, RedemptionResult.idempotent_replay_matched.injEq] at h
        subst r₀
        exact ⟨he, cfg, hc, hv⟩
    · contradiction
  · split at h
    · contradiction
    · split at h
      · contradiction
      · split at h <;> contradiction

theorem decision_not_indeterminate (crypto s q) :
    decision crypto s q ≠ .indeterminate_transaction_state := by
  unfold decision
  split
  · simp
  · split
    · rename_i r he hd
      rcases retry_cases crypto s q r with h | ⟨cfg, hc, hv, h⟩ <;> simp [h]
    · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp

theorem checkNew_sound (crypto cfg q r) (h : checkNew crypto cfg q = some r) :
    keyOf cfg.expected = some q.key ∧
    verifyProvenance crypto cfg.limits cfg.expected q.signed q.snapshot q.profile =
      .ok r.historicalReport ∧
    reportAccepted cfg.allowMissingTimestamp r.historicalReport = true ∧
    crypto.sha256 (bindingOf q).message = .ok r.payloadDigest ∧
    r.pinnedContextVersion = q.contextVersion := by
  cases hv : verifyProvenance crypto cfg.limits cfg.expected q.signed q.snapshot q.profile <;>
    cases hd : crypto.sha256 (bindingOf q).message <;>
    by_cases hk : keyOf cfg.expected = some q.key <;>
    simp_all [checkNew, Except.toOption]
  rcases h with ⟨ha, rfl⟩
  simp [ha]

/-- Exact successful status conjunction, independent of cryptographic-strength claims. -/
theorem reportAccepted_iff (a r) : reportAccepted a r = true ↔
    r.signature = .valid ∧ r.keyAuthorization = .authorized ∧
    r.contextBinding = .matched ∧ r.replay = .challenge_matched ∧
    r.snapshotBinding = .matched ∧ r.profileBinding = .matched ∧
    (r.freshness = .within_trusted_window ∨ (a = true ∧ r.freshness = .no_timestamp)) := by
  simp [reportAccepted]

/-- Classification of changes: unchanged redemption state, or exactly one issued key consumed. -/
def Change (s t : State) : Prop :=
  (t.entries = s.entries ∧ t.accepted = s.accepted) ∨
  (∃ k r, s.entries k = some .issued ∧
    t.entries = put s.entries k (some (.consumed r)) ∧ t.accepted = k :: s.accepted) ∨
  (∃ k, s.entries k = none ∧ t.entries = put s.entries k (some .issued) ∧
    t.accepted = s.accepted)

theorem commit_change (crypto s tx q) : Change s (commitChecked crypto s tx q).1 := by
  unfold commitChecked
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · split
    · exact Or.inl ⟨rfl, rfl⟩
    · rename_i b hb he
      have be : b = bindingOf q := by simpa using he
      subst b
      cases hd : decision crypto s q with
      | newly_consumed r =>
        exact Or.inr (Or.inl ⟨q.key, r, (decision_new _ _ _ _ hd).1, rfl, rfl⟩)
      | idempotent_replay_matched r => exact Or.inl ⟨rfl, rfl⟩
      | rejected e => exact Or.inl ⟨rfl, rfl⟩
      | indeterminate_transaction_state => exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · split <;> exact Or.inl ⟨rfl, rfl⟩

theorem step_change (crypto s i) : Change s (step crypto s i).1 := by
  cases i with
  | installContext v cfg => simp only [step]; split <;> exact Or.inl ⟨rfl, rfl⟩
  | issue k =>
    simp only [step]
    split
    · exact Or.inl ⟨rfl, rfl⟩
    · rename_i h
      have hn : s.entries k = none := by simpa using h
      split
      · exact Or.inl ⟨rfl, rfl⟩
      · split
        · exact Or.inr (Or.inr ⟨k, hn, rfl, rfl⟩)
        · exact Or.inl ⟨rfl, rfl⟩
  | beginTransaction tx q => simp only [step]; split <;> exact Or.inl ⟨rfl, rfl⟩
  | commit tx q => exact commit_change crypto s tx q
  | abort tx => simp only [step]; split <;> exact Or.inl ⟨rfl, rfl⟩
  | lookup k => exact Or.inl ⟨rfl, rfl⟩
  | resolveTransaction k tx => exact Or.inl ⟨rfl, rfl⟩

theorem Change.consumed_preserved {s t : State} (h : Change s t) {k r}
    (hc : s.entries k = some (.consumed r)) : t.entries k = some (.consumed r) := by
  rcases h with ⟨he, _⟩ | ⟨k', r', hi, he, _⟩ | ⟨k', hi, he, _⟩
  · simpa [he] using hc
  · have hn : k ≠ k' := by intro e; subst k'; simp [hc] at hi
    simpa [he, hn] using hc
  · have hn : k ≠ k' := by intro e; subst k'; simp [hc] at hi
    simpa [he, hn] using hc

theorem consumed_record_immutable (crypto s i k r) (h : s.entries k = some (.consumed r)) :
    (step crypto s i).1.entries k = some (.consumed r) :=
  (step_change crypto s i).consumed_preserved h

theorem run_consumed_immutable (crypto s inputs k r) (h : s.entries k = some (.consumed r)) :
    (run crypto s inputs).entries k = some (.consumed r) := by
  induction inputs generalizing s with
  | nil => exact h
  | cons i is ih => exact ih _ (consumed_record_immutable crypto s i k r h)

structure Invariant (s : State) : Prop where
  unique : s.accepted.Nodup
  recorded : ∀ k ∈ s.accepted, ∃ r, s.entries k = some (.consumed r)

theorem initial_invariant : Invariant initial := ⟨by simp [initial], by simp [initial]⟩
theorem invariant_preserved (crypto s i) (h : Invariant s) : Invariant (step crypto s i).1 := by
  rcases step_change crypto s i with ⟨he, hl⟩ | ⟨k, r, hi, he, hl⟩ | ⟨k, hi, he, hl⟩
  · exact ⟨by simpa [hl] using h.unique, by simpa [hl, he] using h.recorded⟩
  · have hn : k ∉ s.accepted := by
      intro hm; obtain ⟨r', hr⟩ := h.recorded k hm; simp [hi] at hr
    constructor
    · simpa [hl] using List.nodup_cons.mpr ⟨hn, h.unique⟩
    · intro x hx
      simp only [hl, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨r, by simp [he]⟩
      · obtain ⟨r', hr⟩ := h.recorded x hx
        exact ⟨r', consumed_record_immutable crypto s i x r' hr⟩
  · constructor
    · simpa [hl] using h.unique
    · intro x hx; obtain ⟨r, hr⟩ := h.recorded x (by simpa [hl] using hx)
      exact ⟨r, consumed_record_immutable crypto s i x r hr⟩

theorem run_invariant (crypto s inputs) (h : Invariant s) : Invariant (run crypto s inputs) := by
  induction inputs generalizing s with
  | nil => exact h
  | cons i is ih => exact ih _ (invariant_preserved crypto s i h)

theorem at_most_one_consumption (crypto inputs) : (run crypto initial inputs).accepted.Nodup :=
  (run_invariant crypto initial inputs initial_invariant).unique

theorem consume_requires_issued (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .newly_consumed r) :
    s.entries q.key = some .issued ∧ s.active q.key.scope = some q.contextVersion ∧
    ∃ cfg, s.contexts q.contextVersion = some cfg ∧ checkNew crypto cfg q = some r := by
  unfold commitChecked at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · exact decision_new crypto s q r h
  · contradiction
  · split at h
    · contradiction
    · exact False.elim (retry_not_new _ _ _ _ _ h)

theorem new_acceptance_effect (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .newly_consumed r) :
    (commitChecked crypto s tx q).1.entries q.key = some (.consumed r) ∧
    (commitChecked crypto s tx q).1.accepted = q.key :: s.accepted := by
  cases ht : s.transactions tx with
  | none => simp [commitChecked, ht] at h
  | some t => cases t with
    | pending b =>
      by_cases hb : b = bindingOf q
      · have hd : decision crypto s q = .newly_consumed r := by
          simpa [commitChecked, ht, hb] using h
        simp [commitChecked, ht, hb, hd, finish, bindingOf]
      · simp [commitChecked, ht, hb] at h
    | aborted b e => simp [commitChecked, ht] at h
    | committed b r₀ kind =>
      by_cases hb : b = bindingOf q
      · have hr : retry crypto s q r₀ = .newly_consumed r := by
          simpa [commitChecked, ht, hb] using h
        exact False.elim (retry_not_new _ _ _ _ _ hr)
      · simp [commitChecked, ht, hb] at h

theorem rejection_preserves_redemption_state (crypto s tx q e)
    (h : (commitChecked crypto s tx q).2 = .rejected e) :
    (commitChecked crypto s tx q).1.entries = s.entries ∧
    (commitChecked crypto s tx q).1.accepted = s.accepted := by
  cases ht : s.transactions tx with
  | none => simp [commitChecked, ht]
  | some t => cases t with
    | pending b =>
      by_cases hb : b = bindingOf q
      · have hd : decision crypto s q = .rejected e := by
          simpa [commitChecked, ht, hb] using h
        simp [commitChecked, ht, hb, hd, finish]
      · simp [commitChecked, ht, hb]
    | aborted b e => simp [commitChecked, ht]
    | committed b r kind =>
      by_cases hb : b = bindingOf q <;> simp [commitChecked, ht, hb]

theorem retry_sound (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .idempotent_replay_matched r) :
    (s.entries q.key = some (.consumed r) ∨
      ∃ kind, s.transactions tx = some (.committed (bindingOf q) r kind)) ∧
    (∃ cfg, s.contexts r.pinnedContextVersion = some cfg ∧ retryValid crypto cfg q r = true) ∧
    (commitChecked crypto s tx q).1.entries = s.entries ∧
    (commitChecked crypto s tx q).1.accepted = s.accepted := by
  cases ht : s.transactions tx with
  | none => simp [commitChecked, ht] at h
  | some t => cases t with
    | pending b =>
      by_cases hb : b = bindingOf q
      · have hd : decision crypto s q = .idempotent_replay_matched r := by
          simpa [commitChecked, ht, hb] using h
        obtain ⟨he, hc⟩ := decision_retry crypto s q r hd
        exact ⟨Or.inl he, hc, by simp [commitChecked, ht, hb, hd, finish],
          by simp [commitChecked, ht, hb, hd, finish]⟩
      · simp [commitChecked, ht, hb] at h
    | aborted b e => simp [commitChecked, ht] at h
    | committed b r₀ kind =>
      by_cases hb : b = bindingOf q
      · have hh : retry crypto s q r₀ = .idempotent_replay_matched r := by
          simpa [commitChecked, ht, hb] using h
        rcases retry_cases crypto s q r₀ with hr | ⟨cfg, hc, hv, hr⟩
        · simp [hr] at hh
        · have he : r₀ = r := by simpa [hr] using hh
          subst r₀
          exact ⟨Or.inr ⟨kind, by simp [hb]⟩, ⟨cfg, hc, hv⟩,
            by simp [commitChecked, ht, hb], by simp [commitChecked, ht, hb]⟩
      · simp [commitChecked, ht, hb] at h

def Terminal : TransactionState → Prop
  | .pending _ => False
  | .committed _ _ _ | .aborted _ _ => True

@[simp] theorem finish_other (s tx b r tx') (h : tx' ≠ tx) :
    (finish s tx b r).transactions tx' = s.transactions tx' := by
  cases r <;> simp [finish, h]

theorem commit_terminal_preserved (crypto s tx q tx' t)
    (h : s.transactions tx' = some t) (ht : Terminal t) :
    (commitChecked crypto s tx q).1.transactions tx' = some t := by
  unfold commitChecked
  split
  · exact h
  · rename_i b hp
    have hn : tx' ≠ tx := by
      intro he; subst tx'; rw [hp] at h
      cases h; exact ht
    split
    · exact h
    · simpa [hn] using h
  · exact h
  · split <;> exact h

theorem terminal_preserved (crypto s i tx t)
    (h : s.transactions tx = some t) (ht : Terminal t) :
    (step crypto s i).1.transactions tx = some t := by
  cases i with
  | installContext v cfg => simp only [step]; split <;> exact h
  | issue k =>
    simp only [step]; split
    · exact h
    · split
      · exact h
      · split <;> exact h
  | beginTransaction id q =>
    simp only [step]; split
    · exact h
    · rename_i hn
      have he : tx ≠ id := by intro e; subst id; simp [h] at hn
      simpa [he] using h
  | commit id q => exact commit_terminal_preserved crypto s id q tx t h ht
  | abort id =>
    simp only [step]; split
    · rename_i b hp
      have he : tx ≠ id := by intro e; subst id; rw [hp] at h; cases h; exact ht
      simpa [he] using h
    · exact h
  | lookup k => exact h
  | resolveTransaction k id => exact h

theorem run_terminal_preserved (crypto s inputs tx t)
    (h : s.transactions tx = some t) (ht : Terminal t) :
    (run crypto s inputs).transactions tx = some t := by
  induction inputs generalizing s with
  | nil => exact h
  | cons i is ih => exact ih _ (terminal_preserved crypto s i tx t h ht)

theorem resolve_read_only (crypto s k tx) :
    (step crypto s (.resolveTransaction k tx)).1 = s := rfl

theorem resolve_committed_iff (s k tx r kind) :
    resolve s k tx = .confirmed_committed r kind ↔
    ∃ b, b.key = k ∧ s.transactions tx = some (.committed b r kind) := by
  unfold resolve
  split <;> simp_all <;> split <;> simp_all

theorem resolve_aborted_iff (s k tx) : resolve s k tx = .confirmed_not_committed ↔
    ∃ b e, b.key = k ∧ s.transactions tx = some (.aborted b e) := by
  unfold resolve
  split <;> simp_all
  split <;> simp_all

theorem resolve_sound (crypto s k tx inputs)
    (h : resolve s k tx = .confirmed_not_committed) :
    resolve (run crypto s inputs) k tx = .confirmed_not_committed ∧
    ∀ q r, (commitChecked crypto (run crypto s inputs) tx q).2 ≠ .newly_consumed r := by
  obtain ⟨b, e, hk, ht⟩ := (resolve_aborted_iff s k tx).mp h
  have hp := run_terminal_preserved crypto s inputs tx (.aborted b e) ht trivial
  constructor
  · exact (resolve_aborted_iff _ _ _).mpr ⟨b, e, hk, hp⟩
  · intro q r; simp [commitChecked, hp]

theorem authorization_blocked (r : ConsumedRecord) :
    r.historicalReport.authorization = .blocked :=
  DigitalProvenanceReportContract.authorization_blocked _

theorem lost_response_no_rollback (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .newly_consumed r) :
    (commitChecked crypto s tx q).1.entries q.key = some (.consumed r) ∧
    delivered true (.redemption (.newly_consumed r)) = none :=
  ⟨(new_acceptance_effect crypto s tx q r h).1, rfl⟩

theorem contexts_unchanged_by_commit (crypto s tx q) :
    (commitChecked crypto s tx q).1.contexts = s.contexts := by
  unfold commitChecked
  split
  · rfl
  · split
    · rfl
    · cases decision crypto s q <;> rfl
  · rfl
  · split <;> rfl

theorem installed_context_immutable (crypto s i v cfg) (h : s.contexts v = some cfg) :
    (step crypto s i).1.contexts v = some cfg := by
  cases i with
  | installContext w c =>
    simp only [step]; split
    · exact h
    · rename_i hn
      have he : v ≠ w := by intro e; subst w; simp [h] at hn
      simpa [he] using h
  | issue k =>
    simp only [step]; split
    · exact h
    · split
      · exact h
      · split <;> exact h
  | beginTransaction tx q => simp only [step]; split <;> exact h
  | commit tx q => simpa only [step, contexts_unchanged_by_commit] using h
  | abort tx => simp only [step]; split <;> exact h
  | lookup k => exact h
  | resolveTransaction k tx => exact h

theorem retry_bindings (crypto cfg q r) (h : retryValid crypto cfg q r = true) :
    InputsFit cfg.limits cfg.expected q.signed q.snapshot q.profile ∧
    crypto.sha256 (bindingOf q).message = .ok r.payloadDigest ∧
    q.snapshot.size = q.signed.manifest.snapshot.sizeBytes ∧
    crypto.sha256 q.snapshot = .ok q.signed.manifest.snapshot.digest ∧
    q.profile.size = q.signed.manifest.profile.sizeBytes ∧
    crypto.sha256 q.profile = .ok q.signed.manifest.profile.digest := by
  simpa only [retryValid, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

/-- Unknown/pending outcomes are not promoted by elapsed time. No timeout finalizer. -/
theorem unresolved_pending (s k tx b) (h : s.transactions tx = some (.pending b)) :
    resolve s k tx = .still_indeterminate := by simp [resolve, h]
theorem unresolved_absent (s k tx) (h : s.transactions tx = none) :
    resolve s k tx = .still_indeterminate := by simp [resolve, h]

theorem transaction_conflict (crypto s tx q b)
    (h : s.transactions tx = some (.pending b)) (hb : b ≠ bindingOf q) :
    commitChecked crypto s tx q = (s, .rejected .transaction_conflict) := by
  simp [commitChecked, h, hb]

/-- The ghost log counts exactly the new-acceptance result, not retries or resolutions. -/
theorem commit_log_exact (crypto s tx q) :
    (commitChecked crypto s tx q).1.accepted =
      match (commitChecked crypto s tx q).2 with
      | .newly_consumed _ => q.key :: s.accepted
      | _ => s.accepted := by
  cases ht : s.transactions tx with
  | none => simp [commitChecked, ht]
  | some t => cases t with
    | pending b =>
      by_cases hb : b = bindingOf q
      · cases hd : decision crypto s q <;> simp [commitChecked, ht, hb, hd, finish, bindingOf]
      · simp [commitChecked, ht, hb]
    | aborted b e => simp [commitChecked, ht]
    | committed b r kind =>
      by_cases hb : b = bindingOf q
      · rcases retry_cases crypto s q r with hr | ⟨cfg, hc, hv, hr⟩ <;>
          simp [commitChecked, ht, hb, hr]
      · simp [commitChecked, ht, hb]


/-- A successful new acceptance excludes any second one, after arbitrary intervening operations. -/
theorem no_second_new_acceptance (crypto s tx first record inputs laterTx later)
    (h : (commitChecked crypto s tx first).2 = .newly_consumed record)
    (hk : later.key = first.key) (r : ConsumedRecord) :
    (commitChecked crypto (run crypto (commitChecked crypto s tx first).1 inputs)
      laterTx later).2 ≠ .newly_consumed r := by
  have hc := run_consumed_immutable crypto (commitChecked crypto s tx first).1 inputs
    first.key record (new_acceptance_effect crypto s tx first record h).1
  intro hn
  have hi := (consume_requires_issued _ _ _ _ _ hn).1
  rw [hk, hc] at hi
  cases hi


structure ChallengeRegistrySuite : Prop where
  requires_issued : ∀ crypto s tx q r,
    (commitChecked crypto s tx q).2 = .newly_consumed r →
    s.entries q.key = some .issued ∧ s.active q.key.scope = some q.contextVersion ∧
    ∃ cfg, s.contexts q.contextVersion = some cfg ∧ checkNew crypto cfg q = some r
  unique : ∀ crypto inputs, (run crypto initial inputs).accepted.Nodup
  immutable : ∀ crypto s inputs k r, s.entries k = some (.consumed r) →
    (run crypto s inputs).entries k = some (.consumed r)
  retry : ∀ crypto s tx q r,
    (commitChecked crypto s tx q).2 = .idempotent_replay_matched r →
    (s.entries q.key = some (.consumed r) ∨
      ∃ kind, s.transactions tx = some (.committed (bindingOf q) r kind)) ∧
    (∃ cfg, s.contexts r.pinnedContextVersion = some cfg ∧ retryValid crypto cfg q r = true) ∧
    (commitChecked crypto s tx q).1.entries = s.entries ∧
    (commitChecked crypto s tx q).1.accepted = s.accepted
  refusal : ∀ crypto s tx q e, (commitChecked crypto s tx q).2 = .rejected e →
    (commitChecked crypto s tx q).1.entries = s.entries ∧
    (commitChecked crypto s tx q).1.accepted = s.accepted
  read_only : ∀ crypto s k tx, (step crypto s (.resolveTransaction k tx)).1 = s
  resolution : ∀ crypto s k tx inputs, resolve s k tx = .confirmed_not_committed →
    resolve (run crypto s inputs) k tx = .confirmed_not_committed ∧
    ∀ q r, (commitChecked crypto (run crypto s inputs) tx q).2 ≠ .newly_consumed r
  blocked : ∀ r : ConsumedRecord, r.historicalReport.authorization = .blocked

theorem verification_suite : ChallengeRegistrySuite :=
  ⟨consume_requires_issued, at_most_one_consumption, run_consumed_immutable, retry_sound,
    rejection_preserves_redemption_state, resolve_read_only, resolve_sound, authorization_blocked⟩

end DigitalProvenanceChallengeRegistryContract

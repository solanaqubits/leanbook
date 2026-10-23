/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DigitalProvenanceRecoveryContract

/-! Exact-content, single-context sequential protocol and its forward simulation
to epsilon259. Durable completion and independent current content anchors are
model premises. This is not a theorem about SQLite system calls, SHA-256,
the HTTPS witness, concurrent executions or physical storage. -/
namespace DigitalProvenanceReadyPreparedContract
open DigitalProvenanceReplayContract
set_option autoImplicit false

abbrev Entries := List ByteArray
inductive Head where
  | ready (epoch : Nat) (entries : Entries)
  | prepared (epoch : Nat) (before after : Entries)
  deriving DecidableEq
inductive Phase where
  | idle | planned | witnessed | durable | sealed
  deriving DecidableEq
structure State where
  completed : Entries
  head : Head
  pending : Option ByteArray
  phase : Phase
  online : Bool
  /-- Ghost output history, never read from the database. -/
  acknowledged : Entries
  deriving DecidableEq

def initial (b : ChallengeRegistry) : State :=
  ⟨[], .ready 0 [], none, .idle, true, b.usedChallenges⟩

/-- Successful durable events only. Errors may stutter or leave the process offline.
An ambiguous completion is represented by either the completion then crash,
or crash without that completion, not by an assertion that a write rolled back. -/
inductive Step (b : ChallengeRegistry) : State → Option ByteArray → State → Prop where
  | stutter (s) : Step b s none s
  | prepare (s q report e)
      (online : s.online = true) (idle : s.phase = .idle)
      (current : s.head = .ready e s.completed)
      (valid : (redeemChallenge (DigitalProvenanceRecoveryContract.registryAt b s.completed)
          q).report = some report) :
      Step b s none { s with pending := some q.expected.challenge, phase := .planned }
  | witnessPrepare (s e c)
      (online : s.online = true) (planned : s.phase = .planned)
      (pending : s.pending = some c) (current : s.head = .ready e s.completed) :
      Step b s none { s with head := .prepared e s.completed (s.completed ++ [c]),
                             phase := .witnessed }
  | sqlCommit (s e c)
      (online : s.online = true) (witnessed : s.phase = .witnessed)
      (pending : s.pending = some c)
      (prepared : s.head = .prepared e s.completed (s.completed ++ [c])) :
      Step b s none { s with completed := s.completed ++ [c], phase := .durable }
  | finalize (s e before)
      (online : s.online = true) (durable : s.phase = .durable)
      (prepared : s.head = .prepared e before s.completed) :
      Step b s none { s with head := .ready (e + 1) s.completed, phase := .sealed }
  | acknowledge (s e c)
      (online : s.online = true) (sealed : s.phase = .sealed)
      (pending : s.pending = some c) (current : s.head = .ready e s.completed)
      (present : c ∈ s.completed) :
      Step b s (some c) { s with pending := none, phase := .idle, acknowledged := c ::
          s.acknowledged }
  | crash (s) :
      Step b s none { s with pending := none, phase := .idle, online := false }
  | recoverPrepared (s e before)
      (offline : s.online = false)
      (exactPostState : s.head = .prepared e before s.completed) :
      Step b s none { s with head := .ready (e + 1) s.completed }
  | recoverReady (s e)
      (offline : s.online = false) (current : s.head = .ready e s.completed) :
      Step b s none { s with online := true, phase := .idle, pending := none }

inductive Execution (b : ChallengeRegistry) : State → List (Option ByteArray) → State → Prop where
  | nil (s) : Execution b s [] s
  | cons {s t u o os} : Step b s o t → Execution b t os u → Execution b s (o :: os) u

def Reachable (b : ChallengeRegistry) (s : State) : Prop :=
  ∃ outputs, Execution b (initial b) outputs s

/-- Exact image is an environmental retention obligation, not a check against
lost pre-crash RAM in a future implementation. Context and base are pinned. -/
def restoreCandidate? (b : ChallengeRegistry) (s : State) (i :
    DigitalProvenanceRecoveryContract.RegistryImage) :
    Option ChallengeRegistry :=
  match s.head with
  | .prepared _ _ _ => none
  | .ready _ entries =>
    if s.online = false ∧ i.base = b ∧ i.entries = s.completed ∧ entries = s.completed then
      some (DigitalProvenanceRecoveryContract.registryAt b s.completed)
    else none

/-- Recovery safety over reachable states and admissible exact images. -/
def RecoverySafety : Prop :=
  ∀ b s i r, Reachable b s → restoreCandidate? b s i = some r →
    s.acknowledged ⊆ r.usedChallenges ∧ r.context = b.context

/-- Finite abstract expansion, including emitted outputs; empty expansion is stutter. -/
def abstractTrace (b : ChallengeRegistry) (s : DigitalProvenanceRecoveryContract.State) :
    List DigitalProvenanceRecoveryContract.Action → DigitalProvenanceRecoveryContract.State × List
        ByteArray
  | [] => (s, [])
  | a :: as =>
    let out := DigitalProvenanceRecoveryContract.step b s a
    let tail := abstractTrace b out.state as
    (tail.1, out.emitted.toList ++ tail.2)

/-- Output-preserving forward simulation; witness finalization during recovery
may stutter in the abstract model. -/
structure ForwardSimulation (b : ChallengeRegistry)
    (rel : State → DigitalProvenanceRecoveryContract.State → Prop) : Prop where
  initial_related : rel (initial b) (DigitalProvenanceRecoveryContract.initial b)
  observations : ∀ s a, rel s a →
    s.completed = a.committed ∧ s.acknowledged = a.acknowledged
  step_matching : ∀ s o t a, Reachable b s → rel s a → Step b s o t →
    ∃ actions, rel t (abstractTrace b a actions).1 ∧
      (abstractTrace b a actions).2 = o.toList
  restoration : ∀ s a i r, Reachable b s → rel s a →
    restoreCandidate? b s i = some r →
    DigitalProvenanceRecoveryContract.restoreRegistry? b.context
        (DigitalProvenanceRecoveryContract.trusted b a) i = some r

/-- Combined correspondence and safety contract, proved below. -/
structure ProofObligations : Prop where
  safety : RecoverySafety
  simulation : ∀ b, ∃ rel, ForwardSimulation b rel


def phaseMap : Phase → DigitalProvenanceRecoveryContract.Phase
  | .idle => .idle
  | .planned | .witnessed => .prepared
  | .durable => .durable
  | .sealed => .anchored

/-- The abstract anchor may lag the concrete head during recovery. Its own
reachability invariant keeps the acknowledged prefix protected. -/
def Related (b : ChallengeRegistry) (s : State) (a : DigitalProvenanceRecoveryContract.State) :
    Prop :=
  DigitalProvenanceRecoveryContract.Reachable b a ∧ a.committed = s.completed ∧
  a.acknowledged = s.acknowledged ∧ a.pending = s.pending ∧
  a.online = s.online ∧ a.phase = phaseMap s.phase ∧
  (s.phase = .sealed → a.anchor = s.completed)

theorem related_initial (b) : Related b (initial b) (DigitalProvenanceRecoveryContract.initial b)
    := by
  refine ⟨⟨[], rfl⟩, ?_⟩
  simp [initial, DigitalProvenanceRecoveryContract.initial, phaseMap]

theorem related_step (b s o t a) (h : Related b s a) (hs : Step b s o t) :
    ∃ actions, Related b t (abstractTrace b a actions).1 ∧
      (abstractTrace b a actions).2 = o.toList := by
  rcases h with ⟨hr, hc, ha, hp, ho, hph, hseal⟩
  cases hs with
  | stutter => exact ⟨[], ⟨hr, hc, ha, hp, ho, hph, hseal⟩, rfl⟩
  | prepare q report e online idle current valid =>
    have he := DigitalProvenanceRecoveryContract.prepare_success b a q report (ho.trans online)
      (by simpa [idle, phaseMap] using hph) (by simpa [hc] using valid)
    have hr' := DigitalProvenanceRecoveryContract.reachable_step b a (.prepare q) hr
    simp only [DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet] at hr'
    refine ⟨[.prepare q], ?_⟩
    simp only [abstractTrace, DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet, Option.toList_none, List.nil_append]
    constructor
    · exact ⟨hr', hc, ha, rfl, ho, rfl, by simp⟩
    · trivial
  | witnessPrepare e c online planned pending current =>
    refine ⟨[], ?_, rfl⟩
    exact ⟨hr, hc, ha, hp, ho, by simpa [abstractTrace, planned, phaseMap] using hph, by simp⟩
  | sqlCommit e c online witnessed pending prepared =>
    have he : DigitalProvenanceRecoveryContract.persist a =
        DigitalProvenanceRecoveryContract.quiet {a with committed := a.committed ++ [c], phase :=
        .durable} := by
      simp [DigitalProvenanceRecoveryContract.persist, ho, online, hph, witnessed, phaseMap, hp,
          pending]
    have hr' := DigitalProvenanceRecoveryContract.reachable_step b a .persist hr
    simp only [DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet] at hr'
    refine ⟨[.persist], ?_⟩
    simp only [abstractTrace, DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet, Option.toList_none, List.nil_append]
    constructor
    · exact ⟨hr', by simp [hc], ha, hp, ho, rfl, by simp⟩
    · trivial
  | finalize e before online durable prepared =>
    have he : DigitalProvenanceRecoveryContract.anchorCommit a =
        DigitalProvenanceRecoveryContract.quiet {a with anchor := a.committed, phase := .anchored}
        := by
      simp [DigitalProvenanceRecoveryContract.anchorCommit, ho, online, hph, durable, phaseMap]
    have hr' := DigitalProvenanceRecoveryContract.reachable_step b a .anchorCommit hr
    simp only [DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet] at hr'
    refine ⟨[.anchorCommit], ?_⟩
    simp only [abstractTrace, DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet, Option.toList_none, List.nil_append]
    constructor
    · exact ⟨hr', hc, ha, hp, ho, rfl, fun _ => hc⟩
    · trivial
  | acknowledge e c online sealed pending current present =>
    have he : DigitalProvenanceRecoveryContract.acknowledge a =
        ⟨{a with pending := none, phase := .idle, acknowledged := c :: a.acknowledged}, some c,
            .blocked⟩ := by
      simp [DigitalProvenanceRecoveryContract.acknowledge, ho, online, hph, sealed, phaseMap, hp,
          pending, hseal sealed, present]
    have hr' := DigitalProvenanceRecoveryContract.reachable_step b a .acknowledge hr
    simp only [DigitalProvenanceRecoveryContract.step, he] at hr'
    refine ⟨[.acknowledge], ?_⟩
    simp only [abstractTrace, DigitalProvenanceRecoveryContract.step, he, Option.toList_some,
        List.append_nil]
    constructor
    · exact ⟨hr', hc, by simp [ha], rfl, ho, rfl, by simp⟩
    · trivial
  | crash =>
    have hr' := DigitalProvenanceRecoveryContract.reachable_step b a .crash hr
    refine ⟨[.crash], ?_⟩
    simp only [abstractTrace, DigitalProvenanceRecoveryContract.step,
        DigitalProvenanceRecoveryContract.crash, DigitalProvenanceRecoveryContract.quiet,
        Option.toList_none, List.nil_append]
    constructor
    · exact ⟨hr', hc, ha, rfl, rfl, rfl, by simp⟩
    · trivial
  | recoverPrepared e before offline exactPostState =>
    exact ⟨[], ⟨hr, hc, ha, hp, ho, hph, hseal⟩, rfl⟩
  | recoverReady e offline current =>
    have hv := DigitalProvenanceRecoveryContract.admissible_restore b a
        (DigitalProvenanceRecoveryContract.image b a) hr rfl
    have he : DigitalProvenanceRecoveryContract.recover b b.context a
        (DigitalProvenanceRecoveryContract.image b a) =
        DigitalProvenanceRecoveryContract.quiet {a with pending := none, phase := .idle, online :=
            true} := by
      simp [DigitalProvenanceRecoveryContract.recover, ho, offline, hv]
    have hr' := DigitalProvenanceRecoveryContract.reachable_step b a (.recover b.context
        (DigitalProvenanceRecoveryContract.image b a)) hr
    simp only [DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet] at hr'
    refine ⟨[.recover b.context (DigitalProvenanceRecoveryContract.image b a)], ?_⟩
    simp only [abstractTrace, DigitalProvenanceRecoveryContract.step, he,
        DigitalProvenanceRecoveryContract.quiet, Option.toList_none, List.nil_append]
    constructor
    · exact ⟨hr', hc, ha, rfl, rfl, rfl, by simp⟩
    · trivial

theorem restore_candidate_fields (b s i r) (h : restoreCandidate? b s i = some r) :
    i.base = b ∧ i.entries = s.completed ∧ r = DigitalProvenanceRecoveryContract.registryAt b
        s.completed := by
  unfold restoreCandidate? at h
  split at h
  · contradiction
  · split at h
    · rename_i guard
      exact ⟨guard.2.1, guard.2.2.1, (Option.some.inj h).symm⟩
    · contradiction

theorem related_restoration (b s a i r) (h : Related b s a)
    (hv : restoreCandidate? b s i = some r) :
    DigitalProvenanceRecoveryContract.restoreRegistry? b.context
        (DigitalProvenanceRecoveryContract.trusted b a) i = some r := by
  obtain ⟨hb, he, rfl⟩ := restore_candidate_fields b s i r hv
  have hi : i = DigitalProvenanceRecoveryContract.image b a := by
    cases i with
    | mk ib ie =>
      cases hb
      cases he
      simp only [DigitalProvenanceRecoveryContract.image, h.2.1]
  simpa [h.2.1] using DigitalProvenanceRecoveryContract.admissible_restore b a i h.1 hi

theorem forward_simulation (b) : ForwardSimulation b (Related b) where
  initial_related := related_initial b
  observations := fun _ _ h => ⟨h.2.1.symm, h.2.2.1.symm⟩
  step_matching := fun _ _ _ _ _ h hs => related_step b _ _ _ _ h hs
  restoration := fun _ _ _ _ _ h hv => related_restoration b _ _ _ _ h hv

theorem execution_related (b s os t) (hx : Execution b s os t) :
    ∀ a, Related b s a → ∃ z, Related b t z := by
  induction hx with
  | nil s => exact fun a h => ⟨a, h⟩
  | cons hs hx ih =>
    intro a h
    obtain ⟨actions, ht, _⟩ := related_step b _ _ _ a h hs
    exact ih _ ht

theorem reachable_related (b s) (h : Reachable b s) : ∃ a, Related b s a := by
  obtain ⟨os, hx⟩ := h
  exact execution_related b _ os s hx _ (related_initial b)

theorem recovery_safety : RecoverySafety := by
  intro b s i r hs hv
  obtain ⟨a, h⟩ := reachable_related b s hs
  have hrestore := related_restoration b s a i r h hv
  constructor
  · simpa [h.2.2.1] using DigitalProvenanceRecoveryContract.crash_recovery_sound b a b.context i r
      h.1 hrestore
  · exact DigitalProvenanceRecoveryContract.restore_context b.context
      (DigitalProvenanceRecoveryContract.trusted b a) i r hrestore

theorem proof_obligations : ProofObligations :=
  ⟨recovery_safety, fun b => ⟨Related b, forward_simulation b⟩⟩



theorem abstractTrace_append (b a xs ys) :
    abstractTrace b a (xs ++ ys) =
      let first := abstractTrace b a xs
      let second := abstractTrace b first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing a with
  | nil => simp [abstractTrace]
  | cons x xs ih => simp [abstractTrace, ih, List.append_assoc]

/-- Every finite execution is matched, including the ordered output history. -/
theorem execution_simulation (b s os t) (hx : Execution b s os t) :
    ∀ a, Related b s a → ∃ actions,
      Related b t (abstractTrace b a actions).1 ∧
      (abstractTrace b a actions).2 = os.flatMap Option.toList := by
  induction hx with
  | nil s => exact fun a h => ⟨[], h, rfl⟩
  | cons hs hx ih =>
    intro a h
    obtain ⟨xs, ht, ho⟩ := related_step b _ _ _ a h hs
    obtain ⟨ys, hu, hout⟩ := ih _ ht
    refine ⟨xs ++ ys, ?_⟩
    simp only [abstractTrace_append, ho, hout, List.flatMap_cons]
    exact ⟨hu, True.intro⟩

/-- Any previously acknowledged raw byte string is rejected after recovery. -/
theorem recovered_replay_rejected (b s i r q) (hs : Reachable b s)
    (hv : restoreCandidate? b s i = some r)
    (hc : q.expected.challenge ∈ s.acknowledged) :
    redeemChallenge r q = reject r := by
  exact DigitalProvenanceReplayContract.used_challenge_rejected r q ((recovery_safety b s i r hs
      hv).1 hc)

theorem restored_base_preserved (b s i r) (hv : restoreCandidate? b s i = some r) :
    b.usedChallenges ⊆ r.usedChallenges := by
  obtain ⟨_, _, rfl⟩ := restore_candidate_fields b s i r hv
  intro c hc
  exact (DigitalProvenanceRecoveryContract.mem_registryAt b s.completed c).mpr (Or.inr hc)

/-- This concerns the formal result field, not external service authorization. -/
theorem abstract_authorization_blocked (b a action) :
    (DigitalProvenanceRecoveryContract.step b a action).authorization = .blocked :=
  DigitalProvenanceRecoveryContract.result_blocked _

end DigitalProvenanceReadyPreparedContract

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DigitalProvenanceVerificationContract

/-! Sequential replay protection relative to the pure provenance verifier.
No concurrency, durable storage, registry rollback recovery or cryptographic
implementation is modeled. Challenge identity is exact byte equality. -/
namespace DigitalProvenanceReplayContract
open DigitalProvenanceManifestContract DigitalProvenanceVerificationContract

/-- Fixed scope of one registry: all expected-context fields except the changing challenge. -/
structure RegistryContext where
  signerId : String
  keyId : String
  roleId : String
  sessionId : String
  policyVersion : String
  n : Nat
  j : Nat
  epsilon : ℚ
  expectedContextId : String
  deriving DecidableEq

def contextOf (e : ExpectedContext) : RegistryContext :=
  ⟨e.signerId, e.keyId, e.roleId, e.sessionId, e.policyVersion,
    e.n, e.j, e.epsilon, e.expectedContextId⟩

/-- A list implements exact membership; initial duplicates do not weaken rejection. -/
structure ChallengeRegistry where
  context : RegistryContext
  usedChallenges : List ByteArray
  deriving DecidableEq

/-- Exact decidable membership, without relying on a separate lawful byte-array BEq instance. -/
def challengeMem (c : ByteArray) : (cs : List ByteArray) → Decidable (c ∈ cs)
  | [] => isFalse (by simp)
  | d :: ds =>
    letI : Decidable (c ∈ ds) := challengeMem c ds
    decidable_of_iff (c = d ∨ c ∈ ds) List.mem_cons.symm

instance (c : ByteArray) (cs : List ByteArray) : Decidable (c ∈ cs) := challengeMem c cs

structure RedemptionRequest where
  limits : ManifestLimits
  backend : CryptoBackend
  policy : VerificationPolicy
  expected : ExpectedContext
  frame : ByteArray
  signature : ByteArray
  snapshot : ByteArray
  profile : ByteArray

def checkedReport (q : RedemptionRequest) : Option VerificationReport :=
  verifyProvenance q.limits q.backend q.policy q.expected q.frame q.signature q.snapshot q.profile

structure RedemptionResult where
  registry : ChallengeRegistry
  report : Option VerificationReport
  authorization : AuthorizationStatus
  deriving DecidableEq

def reject (r : ChallengeRegistry) : RedemptionResult := ⟨r, none, .blocked⟩

def accept (r : ChallengeRegistry) (challenge : ByteArray)
    (report : VerificationReport) : RedemptionResult :=
  ⟨{ r with usedChallenges := challenge :: r.usedChallenges }, some report, .blocked⟩

def redeemChallenge (r : ChallengeRegistry) (q : RedemptionRequest) : RedemptionResult :=
  if r.context = contextOf q.expected then
    match checkedReport q with
    | none => reject r
    | some report =>
      if q.expected.challenge ∈ r.usedChallenges then reject r
      else accept r q.expected.challenge report
  else reject r

def CanRedeem (r : ChallengeRegistry) (q : RedemptionRequest)
    (report : VerificationReport) : Prop :=
  r.context = contextOf q.expected ∧ checkedReport q = some report ∧
    q.expected.challenge ∉ r.usedChallenges

theorem redeem_of_canRedeem (r q report) (h : CanRedeem r q report) :
    redeemChallenge r q = accept r q.expected.challenge report := by
  rcases h with ⟨hc, hv, hn⟩
  simp [redeemChallenge, hc, hv, hn]

theorem redeem_cases (r q) :
    redeemChallenge r q = reject r ∨
      ∃ report, CanRedeem r q report ∧
        redeemChallenge r q = accept r q.expected.challenge report := by
  by_cases hc : r.context = contextOf q.expected
  · cases hv : checkedReport q with
    | none => exact Or.inl (by simp [redeemChallenge, hc, hv])
    | some report =>
      by_cases hu : q.expected.challenge ∈ r.usedChallenges
      · exact Or.inl (by simp [redeemChallenge, hc, hv, hu])
      · exact Or.inr ⟨report, ⟨hc, hv, hu⟩, redeem_of_canRedeem r q report ⟨hc, hv, hu⟩⟩
  · exact Or.inl (by simp [redeemChallenge, hc])

theorem redeem_report_iff (r q report) :
    (redeemChallenge r q).report = some report ↔ CanRedeem r q report := by
  constructor
  · intro h
    rcases redeem_cases r q with hr | ⟨rp, hp, hr⟩
    · simp [hr, reject] at h
    · have he : rp = report := by simpa [hr, accept] using h
      simpa [he] using hp
  · intro h
    rw [redeem_of_canRedeem r q report h]
    rfl

/-- Exact end-to-end criterion, including the canonical verifier and replay guards. -/
theorem redeem_iff (r q m) :
    (redeemChallenge r q).report = some (acceptedReport m) ↔
    r.context = contextOf q.expected ∧
      (FitsManifestLimits q.limits m ∧ encodeManifestV1 m = q.frame ∧
        ManifestAccepted q.backend q.policy q.expected q.snapshot q.profile q.signature m) ∧
      q.expected.challenge ∉ r.usedChallenges := by
  rw [redeem_report_iff]
  unfold CanRedeem checkedReport
  rw [verifyProvenance_iff]

theorem context_mismatch_rejected (r q) (h : r.context ≠ contextOf q.expected) :
    redeemChallenge r q = reject r := by
  simp [redeemChallenge, h]

theorem validation_failure_preserves (r q) (h : checkedReport q = none) :
    redeemChallenge r q = reject r := by
  by_cases hc : r.context = contextOf q.expected <;> simp [redeemChallenge, hc, h]

theorem used_challenge_rejected (r q) (h : q.expected.challenge ∈ r.usedChallenges) :
    redeemChallenge r q = reject r := by
  rcases redeem_cases r q with hr | ⟨_, hp, _⟩
  · exact hr
  · exact False.elim (hp.2.2 h)

theorem rejected_registry_unchanged (r q) (h : (redeemChallenge r q).report = none) :
    (redeemChallenge r q).registry = r := by
  rcases redeem_cases r q with hr | ⟨_, _, hr⟩
  · simp [hr, reject]
  · simp [hr, accept] at h

theorem accepted_registry (r q report)
    (h : (redeemChallenge r q).report = some report) :
    (redeemChallenge r q).registry =
      { r with usedChallenges := q.expected.challenge :: r.usedChallenges } := by
  rw [redeem_of_canRedeem r q report ((redeem_report_iff r q report).mp h)]
  rfl

theorem context_preserved (r q) :
    (redeemChallenge r q).registry.context = r.context := by
  rcases redeem_cases r q with hr | ⟨_, _, hr⟩ <;> simp [hr, reject, accept]

theorem used_monotone (r q) :
    r.usedChallenges ⊆ (redeemChallenge r q).registry.usedChallenges := by
  intro c hc
  rcases redeem_cases r q with hr | ⟨_, _, hr⟩
  · simpa [hr, reject] using hc
  · simp only [hr, accept, List.mem_cons]
    exact Or.inr hc

theorem accepted_consumes (r q report) (h : (redeemChallenge r q).report = some report) :
    q.expected.challenge ∈ (redeemChallenge r q).registry.usedChallenges := by
  rw [accepted_registry r q report h]
  exact List.mem_cons_self

theorem accepted_manifest_consumed (r q m)
    (h : (redeemChallenge r q).report = some (acceptedReport m)) :
    m.challenge ∈ (redeemChallenge r q).registry.usedChallenges := by
  have ha := ((redeem_iff r q m).mp h).2.1.2.2
  have hc : m.challenge = q.expected.challenge := congrArg ExpectedContext.challenge ha.1
  rw [hc]
  exact accepted_consumes r q (acceptedReport m) h

theorem authorization_blocked (result : RedemptionResult) :
    result.authorization = .blocked := by
  cases result.authorization
  rfl

/-- Only ordinary transitions occur in this history; no reset or replacement operation exists. -/
def runRequests (r : ChallengeRegistry) : List RedemptionRequest → ChallengeRegistry
  | [] => r
  | q :: qs => runRequests (redeemChallenge r q).registry qs

theorem run_context_preserved (r qs) : (runRequests r qs).context = r.context := by
  induction qs generalizing r with
  | nil => rfl
  | cons q qs ih =>
    exact (ih (redeemChallenge r q).registry).trans (context_preserved r q)

theorem run_used_monotone (r qs) : r.usedChallenges ⊆ (runRequests r qs).usedChallenges := by
  induction qs generalizing r with
  | nil => exact fun _ h => h
  | cons q qs ih =>
    exact fun _ h => ih _ (used_monotone r q h)

theorem replay_after_history (r qs q) (h : q.expected.challenge ∈ r.usedChallenges) :
    redeemChallenge (runRequests r qs) q = reject (runRequests r qs) :=
  used_challenge_rejected _ q (run_used_monotone r qs h)

/-- Arbitrary intervening requests and changed policies cannot reuse consumed bytes. -/
theorem accepted_replay_after_history (r first report qs later)
    (ha : (redeemChallenge r first).report = some report)
    (hc : later.expected.challenge = first.expected.challenge) :
    redeemChallenge (runRequests (redeemChallenge r first).registry qs) later =
      reject (runRequests (redeemChallenge r first).registry qs) := by
  apply replay_after_history
  rw [hc]
  exact accepted_consumes r first report ha

structure ProvenanceReplaySuite : Prop where
  exact_acceptance : ∀ r q report,
    (redeemChallenge r q).report = some report ↔ CanRedeem r q report
  failure_preserves : ∀ r q, checkedReport q = none → redeemChallenge r q = reject r
  refusal_preserves : ∀ r q, (redeemChallenge r q).report = none →
    (redeemChallenge r q).registry = r
  history_monotone : ∀ r qs, r.usedChallenges ⊆ (runRequests r qs).usedChallenges
  history_context : ∀ r qs, (runRequests r qs).context = r.context
  replay_rejected : ∀ r qs q, q.expected.challenge ∈ r.usedChallenges →
    redeemChallenge (runRequests r qs) q = reject (runRequests r qs)
  accepted_replay : ∀ r first report qs later,
    (redeemChallenge r first).report = some report →
    later.expected.challenge = first.expected.challenge →
    redeemChallenge (runRequests (redeemChallenge r first).registry qs) later =
      reject (runRequests (redeemChallenge r first).registry qs)
  blocked : ∀ result : RedemptionResult, result.authorization = .blocked

theorem verification_suite : ProvenanceReplaySuite where
  exact_acceptance := redeem_report_iff
  failure_preserves := validation_failure_preserves
  refusal_preserves := rejected_registry_unchanged
  history_monotone := run_used_monotone
  history_context := run_context_preserved
  replay_rejected := replay_after_history
  accepted_replay := accepted_replay_after_history
  blocked := authorization_blocked
end DigitalProvenanceReplayContract

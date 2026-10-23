import Verification.DigitalProvenanceChallengeRegistryContract

/-! Contract examples for the existing ε262 API; no new acceptance semantics.
Historical return is not fresh signature/key/time verification or authorization.
These are sequential mathematical statements, not Python/SQLite refinement. -/
namespace ReplaySemanticsRegression
open DigitalProvenanceChallengeRegistryContract

theorem historical_preserves_consumption (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .idempotent_replay_matched r) :
    (commitChecked crypto s tx q).1.entries = s.entries ∧
    (commitChecked crypto s tx q).1.accepted = s.accepted :=
  ⟨(retry_sound crypto s tx q r h).2.2.1, (retry_sound crypto s tx q r h).2.2.2⟩

theorem historical_uses_pinned_context (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .idempotent_replay_matched r) :
    ∃ cfg, s.contexts r.pinnedContextVersion = some cfg ∧
      retryValid crypto cfg q r = true :=
  (retry_sound crypto s tx q r h).2.1

theorem matching_retry_returns_history (crypto s q r cfg)
    (hc : s.contexts r.pinnedContextVersion = some cfg)
    (hv : retryValid crypto cfg q r = true) :
    retry crypto s q r = .idempotent_replay_matched r := by
  simp [retry, hc, hv]

theorem different_digest_rejected (crypto s q r)
    (hc : s.entries q.key = some (.consumed r))
    (hd : crypto.sha256 (bindingOf q).message ≠ .ok r.payloadDigest) :
    decision crypto s q = .rejected .challenge_already_used := by
  simp [decision, hc, hd]

theorem no_second_consumption_after_history (crypto s tx first r inputs laterTx later)
    (h : (commitChecked crypto s tx first).2 = .newly_consumed r)
    (hk : later.key = first.key) (r' : ConsumedRecord) :
    (commitChecked crypto (run crypto (commitChecked crypto s tx first).1 inputs)
      laterTx later).2 ≠ .newly_consumed r' :=
  no_second_new_acceptance crypto s tx first r inputs laterTx later h hk r'

theorem response_loss_retains_record (crypto s tx q r)
    (h : (commitChecked crypto s tx q).2 = .newly_consumed r) :
    (commitChecked crypto s tx q).1.entries q.key = some (.consumed r) ∧
    delivered true (.redemption (.newly_consumed r)) = none :=
  lost_response_no_rollback crypto s tx q r h

theorem refusal_preserves_consumption (crypto s tx q reason)
    (h : (commitChecked crypto s tx q).2 = .rejected reason) :
    (commitChecked crypto s tx q).1.entries = s.entries ∧
    (commitChecked crypto s tx q).1.accepted = s.accepted :=
  rejection_preserves_redemption_state crypto s tx q reason h

theorem historical_report_stays_blocked (r : ConsumedRecord) :
    r.historicalReport.authorization = .blocked := authorization_blocked r

#print axioms historical_preserves_consumption
#print axioms historical_uses_pinned_context
#print axioms matching_retry_returns_history
#print axioms different_digest_rejected
#print axioms no_second_consumption_after_history
#print axioms response_loss_retains_record
#print axioms refusal_preserves_consumption
#print axioms historical_report_stays_blocked
end ReplaySemanticsRegression

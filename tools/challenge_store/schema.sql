CREATE TABLE context_versions (
 version_id TEXT PRIMARY KEY NOT NULL,
 context_id TEXT NOT NULL, session_id TEXT NOT NULL, policy_version TEXT NOT NULL,
 config TEXT NOT NULL CHECK(json_valid(config)),
 UNIQUE(context_id,session_id,policy_version,version_id)
) STRICT;
CREATE TABLE active_contexts (
 context_id TEXT NOT NULL, session_id TEXT NOT NULL, policy_version TEXT NOT NULL,
 version_id TEXT NOT NULL,
 PRIMARY KEY(context_id,session_id,policy_version),
 FOREIGN KEY(context_id,session_id,policy_version,version_id)
 REFERENCES context_versions(context_id,session_id,policy_version,version_id)
) STRICT;
CREATE TABLE challenge_entries (
 context_id TEXT NOT NULL, session_id TEXT NOT NULL, policy_version TEXT NOT NULL,
 challenge BLOB NOT NULL, entry_state TEXT NOT NULL CHECK(entry_state IN ('ISSUED','CONSUMED')),
 payload_digest BLOB, pinned_version TEXT, report TEXT,
 PRIMARY KEY(context_id,session_id,policy_version,challenge),
 FOREIGN KEY(context_id,session_id,policy_version,pinned_version)
 REFERENCES context_versions(context_id,session_id,policy_version,version_id),
 CHECK((entry_state='ISSUED' AND payload_digest IS NULL AND pinned_version IS NULL AND report IS NULL)
 OR (entry_state='CONSUMED' AND payload_digest IS NOT NULL AND length(payload_digest)=32
 AND pinned_version IS NOT NULL AND report IS NOT NULL AND json_valid(report)))
) STRICT;
CREATE TABLE transactions (
 tx_id TEXT PRIMARY KEY NOT NULL,
 context_id TEXT NOT NULL, session_id TEXT NOT NULL, policy_version TEXT NOT NULL,
 challenge BLOB NOT NULL, signing_message BLOB NOT NULL,
 tx_state TEXT NOT NULL CHECK(tx_state IN ('PENDING','COMMITTED','ABORTED')),
 acceptance_kind TEXT CHECK(acceptance_kind IN ('newAcceptance','historicalReturn')),
 rejection_reason TEXT CHECK(rejection_reason IN ('challenge_already_used','challenge_not_issued',
 'verification_rejected','context_changed','transaction_conflict','transaction_not_started','transaction_aborted')),
 acceptance_order INTEGER UNIQUE,
 CHECK((tx_state='PENDING' AND acceptance_kind IS NULL AND rejection_reason IS NULL AND acceptance_order IS NULL)
 OR (tx_state='ABORTED' AND acceptance_kind IS NULL AND rejection_reason IS NOT NULL AND acceptance_order IS NULL)
 OR (tx_state='COMMITTED' AND acceptance_kind IS NOT NULL AND rejection_reason IS NULL
 AND ((acceptance_kind='newAcceptance' AND acceptance_order IS NOT NULL AND acceptance_order>0)
 OR (acceptance_kind='historicalReturn' AND acceptance_order IS NULL))))
) STRICT;
CREATE UNIQUE INDEX one_new_acceptance ON transactions(context_id,session_id,policy_version,challenge)
 WHERE tx_state='COMMITTED' AND acceptance_kind='newAcceptance';
CREATE TRIGGER context_no_update BEFORE UPDATE ON context_versions BEGIN SELECT RAISE(ABORT,'immutable context'); END;
CREATE TRIGGER context_no_delete BEFORE DELETE ON context_versions BEGIN SELECT RAISE(ABORT,'immutable context'); END;
CREATE TRIGGER active_no_delete BEFORE DELETE ON active_contexts BEGIN SELECT RAISE(ABORT,'no removal'); END;
CREATE TRIGGER active_new_version BEFORE UPDATE ON active_contexts
 WHEN NEW.version_id=OLD.version_id OR NEW.context_id!=OLD.context_id OR NEW.session_id!=OLD.session_id OR NEW.policy_version!=OLD.policy_version
 BEGIN SELECT RAISE(ABORT,'invalid active update'); END;
CREATE TRIGGER entry_insert BEFORE INSERT ON challenge_entries WHEN NEW.entry_state!='ISSUED'
 BEGIN SELECT RAISE(ABORT,'must issue first'); END;
CREATE TRIGGER entry_update BEFORE UPDATE ON challenge_entries
 WHEN OLD.entry_state!='ISSUED' OR NEW.entry_state!='CONSUMED' OR
 OLD.context_id!=NEW.context_id OR OLD.session_id!=NEW.session_id OR OLD.policy_version!=NEW.policy_version OR OLD.challenge!=NEW.challenge
 BEGIN SELECT RAISE(ABORT,'invalid entry transition'); END;
CREATE TRIGGER entry_delete BEFORE DELETE ON challenge_entries BEGIN SELECT RAISE(ABORT,'no removal'); END;
CREATE TRIGGER tx_insert BEFORE INSERT ON transactions WHEN NEW.tx_state!='PENDING'
 BEGIN SELECT RAISE(ABORT,'must register first'); END;
CREATE TRIGGER tx_update BEFORE UPDATE ON transactions
 WHEN OLD.tx_state!='PENDING' OR NEW.tx_state='PENDING' OR OLD.tx_id!=NEW.tx_id OR
 OLD.context_id!=NEW.context_id OR OLD.session_id!=NEW.session_id OR OLD.policy_version!=NEW.policy_version OR
 OLD.challenge!=NEW.challenge OR OLD.signing_message!=NEW.signing_message
 BEGIN SELECT RAISE(ABORT,'invalid transaction transition'); END;
CREATE TRIGGER tx_committed BEFORE UPDATE ON transactions WHEN NEW.tx_state='COMMITTED' AND NOT EXISTS (
 SELECT 1 FROM challenge_entries e WHERE e.context_id=NEW.context_id AND e.session_id=NEW.session_id
 AND e.policy_version=NEW.policy_version AND e.challenge=NEW.challenge AND e.entry_state='CONSUMED')
 BEGIN SELECT RAISE(ABORT,'missing consumed entry'); END;
CREATE TRIGGER tx_delete BEFORE DELETE ON transactions BEGIN SELECT RAISE(ABORT,'no removal'); END;
PRAGMA user_version=1;
-- Previously installed versions cannot be reactivated (ABA exclusion).
CREATE TRIGGER active_no_reactivation BEFORE UPDATE ON active_contexts
 WHEN (SELECT rowid FROM context_versions WHERE version_id=NEW.version_id)
 <= (SELECT rowid FROM context_versions WHERE version_id=OLD.version_id)
 BEGIN SELECT RAISE(ABORT,'context rollback'); END;

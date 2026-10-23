# Corrected SQLite runtime: source distribution

The execution profile is a host-specific example with an /opt installation path.
No corrected binary, system library, credential, or publisher signature is shipped.
A reviewed deployment must qualify its exact SQLite artifact AND CPython extension,
then explicitly install the artifact. The matching original private artifact SHA-256
is recorded in profile.json; the public example path has not been deployed.
Do not silently relax the pin or use the system SQLite as a fallback.

```sh
python3 -m tools.challenge_store.runtime install --source /reviewed/libsqlite3.so.0.8.6
python3 -m tools.challenge_store.runtime check
python3 -m tools.challenge_store.runtime run -- --db /protected/registry.db --config /protected/deployment.json --config-sha256 REVIEWED_HASH inspect
```

The target directory and ancestors must satisfy owner/permission checks. Install
is exclusive, refuses replacement and does not build/download/reset/provision.
Check/run launch a fresh interpreter and verify the mapped artifact before opening
any registry file (an in-memory probe is used). LD_PRELOAD/LD_AUDIT are rejected.
Trusted owner/root/ACL and loader TOCTOU assumptions remain. SHA-256 does not prove
publisher identity. See [test setup](../../docs/provenance-test-setup.en.md).

checkpoint_profile_v1.json is byte-identical to the old format identity; it is NOT
permission to load the old SQLite. Execution qualification uses profile.json.
The SQL schema, digest domain and logical normalization are preserved. Tested
legacy compatibility is not a universal formal compatibility proof.

Stop old writers, preserve consistent backup and independent head evidence,
qualify the new process, inspect guarded state and resolve known transactions before
resuming a real registry. Prepared/indeterminate never permits reset or new genesis.
No production migration or external Witness connection has occurred here.

Native tests are explicitly gated by PROVENANCE_STORE_LIVE_TESTS=1, distinct from
ordinary LEAN_VERIFIER_LIVE_TESTS=1. On a QUALIFIED target, start a new interpreter
with LD_LIBRARY_PATH equal to the protected profile library directory, build via
python3 -m tools.challenge_store.build, then run:

```sh
PROVENANCE_STORE_LIVE_TESTS=1 python3 -m unittest tests.test_challenge_store tests.test_provenance_anchor tests.test_provenance_files tests.test_anchored_cli tests.test_witness_config tests.test_witness_https tests.test_sqlite_runtime -v
```

An unset opt-in means native acceptance is NOT RUN; skipped tests are not evidence
of qualification. Generic public CI remains formal/portable regression only.

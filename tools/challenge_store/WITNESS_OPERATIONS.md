# Witness deployment configuration and operations v1

This layer prepares an external provider connection; it does not deploy, enroll or
qualify a provider. `witness_config` supplies an explicit POSIX trusted-host loader
and two diagnostic commands. Existing Store/submit-files CLI behavior is unchanged.
No command here opens the local registry, performs CAS, resolves a transaction or
resets an anchor. Remote reads may still create service audit/access log entries.

## Independently trusted deployment input

The controller supplies an absolute configuration path **and** its expected SHA-256
through a trusted channel outside submitted artifacts and the rollbackable registry.
The expected digest must not be derived automatically from that same local file at
startup. Pinning a file to its own freshly computed digest establishes no trust.
The expected pin is not a secret, and need not be publicly posted. Protect its
distribution and rollback history as part of controller policy.

Example schema (placeholders, not usable production credentials):

```json
{
  "schema": "witness-deployment/v1",
  "deployment_id": "reviewed-provider",
  "revision": "reviewed-revision-1",
  "store_id": "independently-pinned-store",
  "transport": {
    "host": "witness.example.invalid",
    "port": 443,
    "server_id": "independently-pinned-service",
    "ca_file": "/protected/witness/revision-1/ca.pem",
    "client_cert": "/protected/witness/revision-1/client.pem",
    "client_key": "/protected/witness/revision-1/client.key",
    "server_cert_sha256": "REPLACE_WITH_REVIEWED_LOWERCASE_SHA256_OF_SERVER_LEAF_DER",
    "timeout_seconds": 5
  }
}
```

All fields are mandatory; unknown/duplicate fields, invalid UTF-8 and nonfinite
numbers fail. The configuration file is capped at 16 KiB. JSON whitespace is allowed
and affects the exact file pin. Identifiers are nonempty, <=256 UTF-8 bytes and have
no ASCII control characters. Paths must be absolute with no parent traversal;
neither environment substitution nor home expansion is performed. Transport retains
the TLS1.3/CA/SAN/exact leaf pin rules in [WITNESS_HTTPS.md](WITNESS_HTTPS.md).

Local files must be regular, owned by the effective user or root, and not writable
by group/others. The key additionally has no group/other permissions (normally 0600).
Final-component symlinks and FIFOs/devices are refused. Credential files are capped
at 64 KiB each. Configuration is hashed before TLS credentials are processed. The
CA/client certificate/private-key pair is parsed locally with no network access.
Encrypted PEM keys fail without interactive password input; secret-manager/HSM
integration is outside this file-based profile. Never commit real private keys.

These checks assume a protected host, ancestor directories, ACLs and mount namespace.
They do not defeat a malicious owner/root or changes between checking files and
OpenSSL reopening paths. Use immutable, access-controlled per-revision directories.
The configuration hash pins **configuration bytes**, not certificate-file contents
or monotonically increasing revision order. Replacement of referenced credentials,
revocation and rollback prevention require the controller's separate lifecycle policy.
Reusing an old configuration/pin pair cannot be detected by this stateless loader.

## Read-only commands and reports

```sh
python3 -m tools.challenge_store.witness_config check-config \
  --config /protected/witness/revision-1/deployment.json \
  --config-sha256 REVIEWED_CONFIGURATION_SHA256

python3 -m tools.challenge_store.witness_config probe \
  --config /protected/witness/revision-1/deployment.json \
  --config-sha256 REVIEWED_CONFIGURATION_SHA256
```

`check-config` parses local configuration/credentials only. It cannot check the remote
certificate, remote client ACL, fresh state or local DB consistency. `probe` additionally
performs exactly one authenticated read for the pinned store ID, with no automatic
retry. Do not run it against a service until its address/identity and access are approved
by the controller. It does not contact any endpoint discovered from an incoming packet.

| Report status | Exit | Meaning |
| --- | --- | --- |
| `configuration_valid` | 0 | Local schema, file policy and TLS context initialized |
| `ready_head_observed` | 0 | Authenticated typed Ready observed for this request |
| `prepared_head_observed` | 3 | Prepared observed; use the existing recovery procedure separately |
| `store_not_provisioned` | 3 | Service explicitly returned null; no enrollment attempted |
| `refused` | 1 | Configuration, credential, transport or response check failed |

Argument syntax errors use argparse exit 2. JSON reports contain public deployment/
revision/store/service IDs and the config digest, never key material, credential paths
or Prepared tokens. Errors expose stable codes, not nested exception text. Retain reports
under local audit policy; IDs, checkpoint digests and config hashes may be sensitive
metadata. Every report has `authorization = blocked` and `external_service_qualified = false`.

Exit 0 is **not** a production-readiness or write-authorization decision. A Ready head
is an observation at read time, can change immediately, and is not compared with a
local SQLite checkpoint. An authenticated server can answer with stale state and a
fresh nonce. The probe does not establish anti-rollback, linearizability, durability,
certificate revocation status, local SQL runtime safety or physical provenance.
Timeout remains per blocking socket operation, not a global time/CPU/memory bound.

## Application use

```python
from tools.challenge_store.witness_config import load_deployment
from tools.challenge_store.anchor import AnchoredStore

deployment = load_deployment(config_path, expected_sha256=controller_config_pin)
witness = deployment.make_witness()
# This is an application operation, distinct from the read-only probe commands.
with AnchoredStore(db_path, store_id=deployment.store_id,
                   witness=witness, controller=controller) as store:
    result = store.resolve(challenge_key, transaction_id)
```

All protected writers must use the anchored adapter. A successful probe does not
protect direct Store/SQL access or legacy CLI usage. Typed construction and a local
JSON receipt do not authenticate arbitrary client-supplied verification reports.

## Controller deployment and recovery procedure

1. Qualify the independently administered service: store-scoped mTLS ACLs, exclusive
   provisioning, authoritative fresh reads, exact full-head CAS, durable acknowledgement,
   restart/failover behavior, independent state rollback protection and audit retention.
   Record evidence and its scope; a boolean in this config cannot self-certify these.
2. Qualify the actual local runtime/dependencies and storage configuration separately.
   The concurrent SQLite WAL-reset/runtime audit is a separate stream; this change
   neither updates SQLite nor establishes vendor-patch qualification.
3. Issue least-privilege client credentials, verify the service CA/SAN/leaf fingerprint
   independently, prepare immutable local configuration/credential files, and install
   the expected configuration pin in the controller's trusted settings. Do not use TOFU.
4. In an exclusive maintenance window follow [ANCHOR.md](ANCHOR.md) for checkpoint
   review and separately authorized first provisioning. Missing state is not permission
   to recreate a previously used store. This client supplies no provisioning endpoint.
5. Run local check, then read-only probe. Compare/validate the local checkpoint through
   the existing AnchoredStore gate; the probe alone is insufficient. Exercise actual
   infrastructure acceptance and failure/recovery procedures before enabling writers.
6. On transport failure or Prepared, preserve identity/pins and existing records. Lost
   CAS acknowledgement may conceal a durable write. Use fresh authenticated state and
   existing checkpoint recovery; never infer rollback from timeout, delete the witness
   slot, downgrade TLS, bypass the gate or switch to a local fallback automatically.

Certificate renewal/CA or client rotation uses a new reviewed revision, independently
distributed pin, immutable files and a controlled client restart. Test new identity/ACLs
before retiring old credentials; drain writers as required. Revoke compromised old keys
at the service and controller. Automatic CRL/OCSP handling is not implemented here.
Emergency recovery never reactivates a revoked/old configuration merely to make a test
pass. Provider migration needs a separate checkpoint continuity/cutover protocol; simply
pointing at a fresh empty service or resetting epochs is not a valid migration.

## Evidence boundary

Conformance tests use temporary local PKI and the previous loopback server. They verify
config refusal, read-only requests, redacted outputs, noninteractive credential failure
and report semantics. No real provider is connected or production-qualified; no new
Lean proof/axiom audit, power-loss test or hardware authorization is claimed.

Implementation references: Python 3.12 [file descriptors and flags](https://docs.python.org/3.12/library/os.html)
and [SSLContext credentials](https://docs.python.org/3.12/library/ssl.html).

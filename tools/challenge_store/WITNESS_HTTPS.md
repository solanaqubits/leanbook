# Witness HTTPS v1 transport and service contract

`HTTPSWitness` implements the existing `Witness` read/CAS API over explicit TLS 1.3
mutual authentication. It is a client, not a deployed production witness service.
The loopback server in tests is a test fixture; its SQLite DB is rollbackable and
must never be presented as independent Anti-Rollback infrastructure.

## Trusted configuration

Supply `WitnessTLSConfig(host, port, server_id, ca_file, client_cert, client_key,
server_cert_sha256, timeout_seconds)` from the controller, independently of incoming
packets and the rollbackable registry. host is an ASCII DNS name or IPv4 address;
IPv6 literal syntax is outside v1. The client validates the CA chain, validity period,
SAN hostname, and exact SHA-256 of the server leaf DER certificate before HTTP data.
The certificate pin must come from a trusted external channel, not a first connection.
Certificate renewal requires an explicitly reviewed new pin/configuration.

TLS 1.3 is required, with no downgrade. The SSL context uses the specified CA file
and mandatory client cert/key; no environment proxy discovery or key-log environment
setting is enabled. Certificate revocation distribution/rotation and file permissions
remain deployment obligations; no CRL/OCSP validation service is silently implied.
Use a least-privilege client identity bound server-side to an allowed store-ID set.
A valid client certificate alone does not grant access to every store or enrollment.

```python
from pathlib import Path
from tools.challenge_store.witness_https import HTTPSWitness, WitnessTLSConfig
from tools.challenge_store.anchor import AnchoredStore

# All values below come from separately reviewed deployment configuration.
witness = HTTPSWitness(WitnessTLSConfig(
    host, port, server_id, Path(ca_file), Path(client_cert), Path(client_key),
    server_leaf_sha256, timeout_seconds=5.0))
with AnchoredStore(db_path, store_id=independently_pinned_id,
                   witness=witness, controller=controller) as registry:
    result = registry.resolve(challenge_key, transaction_id)
```

The existing CLI remains plain Store. This module does not create an endpoint,
issue credentials, change trust roots, enroll a store or replace a missing head.
No public listener is started; tests bind only loopback with ephemeral credentials.

## Wire protocol

Each call creates one TLS connection and sends one POST `/v1/witness`. Canonical ASCII
JSON uses sorted keys, compact separators, escaped Unicode and no extra whitespace.
Duplicate keys, unknown fields and wrong scalar types are rejected. Bodies are capped
at 8192 bytes. Response Content-Length is mandatory and singular; chunked/compressed
responses, duplicate lengths, incorrect MIME/cache headers and non-200 statuses fail.
The response requires `Content-Type: application/json` and `Cache-Control: no-store`.
HTTP framing determines the body boundary; this is not a file-EOF protocol. Connections
are closed after the call. The stdlib bounds HTTP header lines/count separately.

Read request:

```json
{"nonce":"<64 lowercase hex>","operation":"read","server_id":"<pinned service>","store_id":"<external ID>","version":1}
```

CAS adds `expected` and `desired` heads. Head encodings:

```json
{"digest":"<64 hex>","epoch":0,"kind":"ready"}
{"digest":"<64 hex>","epoch":0,"kind":"prepared","next_digest":"<64 hex>","token":"<32 hex>"}
```

The exact previously specified `valid_transition` rule applies: Ready→Prepared keeps
epoch/previous digest; Prepared→Ready increments epoch and uses next_digest. No reset,
expiry, rollback or network enrollment operation exists. Server-side CAS must validate
both the allowed transition and equality of the entire expected head, including token.

Response fields are exactly: version, server_id, store_id, nonce, operation,
request_sha256, result. The first five match the request; request_sha256 hashes the
exact transmitted canonical bytes, including CAS arguments. `read` result is a typed
head or explicit null for authoritative absence; `cas` result is a strict JSON bool.
A conflict is HTTP 200 with false only when the server has definitively performed no
write. HTTP 404/409/503, malformed replies, socket errors or lost responses are errors,
not absence/false. Unknown CAS outcomes propagate through AnchoredStore as indeterminate.

Nonce matching rejects a captured prior response to another request. It does **not**
prove that an authenticated server selected its latest state: a faulty/malicious or
rolled-back service can construct a fresh response containing an old head. Fresh
linearizable reads remain a substantive external contract, not a result of TLS/nonce.

## Timeouts, retries and failures

Socket blocking operations have a configured positive timeout up to 30 seconds.
This is not a total wall-clock deadline: DNS, OS behavior and a continuously trickling
peer can exceed it. Body/header limits do not prove a universal memory/time bound.
There are no implicit retries, redirects, caching or local fallback. A retry policy
must first resolve the external head and use the existing checkpoint recovery rules.
A lost CAS response may hide a durable write. A failed read cannot establish absence.
Exception messages expose stable classifications, not private keys/request bodies.

## External service acceptance obligations (not implemented by the client)

- Independently administered persistent state, resistant to its own snapshot rollback;
  the same-host test SQLite/WAL file does not satisfy this.
- Authenticated fresh reads against the authoritative linearizable state; no replica
  lag/cached head presented as current. No success during uncertain failover.
- Durable atomic CAS with exact expected-head equality and transition validation;
  acknowledge true only after durable completion. Crash/lost reply outcomes resolvable
  by a fresh read, never guessed from timeout.
- Stable service/store identities; exclusive separately authorized provisioning;
  immutable histories or independently trusted monotone anchor, no automatic reset.
- mTLS identity-to-store authorization, protected key storage, certificate rotation and
  revocation policy, capacity limits, audit and operational recovery procedures.
- Tests of restart/failover/rollback boundaries on the selected actual infrastructure.

The test fixture enforces mTLS identity/scope, transition checks and SQLite CAS for
transport/concurrency tests. Restart tests establish only finite local persistence.
No production provider is connected or qualified by this code; hardware authorization
stays blocked and the Third Obligation remains OPEN. No new formal Lean proof is claimed.

References: Python 3.12 [http.client](https://docs.python.org/3.12/library/http.client.html)
and [ssl](https://docs.python.org/3.12/library/ssl.html); the implementation uses this
runtime's existing standard library and records runtime versions in the test receipt.

During concurrent writes a reader may hold an older SQLite WAL snapshot while the
witness has already advanced to Ready for the newer state. `anchor_state_mismatch`
is a safe refusal in this interleaving as well as in genuine rollback. A new read
transaction can align with the current state; the transport never silently retries
CAS or rewrites an anchor. A deterministic regression covers this distinction.

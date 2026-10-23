# Explicit anchored operational CLI

For the consolidated operational procedure and unfilled acceptance record, see
[DEPLOYMENT.en.md](DEPLOYMENT.en.md). It does not qualify or connect a provider.

Use the [qualified runtime launcher](RUNTIME.en.md):
`python3 -m tools.challenge_store.runtime run -- <global flags> <operation>`.
The direct module examples below require an already qualified child-process loader
environment; the original system SQLite is refused by the current runtime profile.

`python3 -m tools.challenge_store.anchored_cli` connects the existing pinned deployment
loader, HTTPSWitness and AnchoredStore to four explicit operations. It is a trusted-host
tool for an already initialized/provisioned registry, not a remote service or independent
Anti-Rollback provider. It does not replace the legacy plain `cli` module.

## Commands

All global flags precede the operation. Supply the expected config digest independently
through the controller, following [WITNESS_OPERATIONS.md](WITNESS_OPERATIONS.md).

```sh
python3 -m tools.challenge_store.anchored_cli \
  --db /protected/registry.db \
  --config /protected/witness/revision-1/deployment.json \
  --config-sha256 REVIEWED_CONFIG_SHA256 \
  inspect
```

Use the same global flags with one of these operations:

| Operation | Arguments | Input JSON fields |
| --- | --- | --- |
| `inspect` | none | No input file accepted |
| `lookup` | `--input request.json` | Exactly `key` |
| `resolve` | `--input request.json` | Exactly `key`, `txId` |
| `submit-files` | `--input request.json --context-version VERSION --manifest MANIFEST --signature SIGNATURE --snapshot SNAPSHOT --profile PROFILE` | Exactly `txId` |

Example resolve envelope:

```json
{"key":{"scope":{"contextId":"context","sessionId":"session","policyVersion":"policy"},"challenge":[1,2,3]},"txId":"previously-chosen-transaction"}
```

Request metadata must be a regular file, <=16 KiB, strict UTF-8 JSON without duplicate
or extra fields. IDs are nonempty, <=256 UTF-8 bytes, without ASCII control characters;
challenge is a list of actual integers in [0,255], never booleans. The database path
must be absolute, with no parent traversal. The four submitted files retain the existing
EOF/canonical decoding/signature-size/dynamic-limit checks and per-file 128 KiB ceiling.
No client-provided positive verification report, key registry or expected context is
accepted in the metadata envelope. Context is obtained through the existing store API.

## What executes

1. Validate the command's metadata before creating a store or client.
2. Load and validate the independently pinned deployment and TLS credentials.
3. Open only `AnchoredStore` with `deployment.store_id` and the explicit HTTPSWitness.
4. Dispatch the selected operation using the existing checkpoint gate and file pipeline.

No preliminary successful `probe` is treated as permission to bypass checkpoint
validation. A Ready from another store/checkpoint is refused by the actual gate.
No direct Store fallback, implicit initialization, enrollment, automatic retry, recovery,
transaction cancellation or anchor reset is exposed. Administrative capabilities remain
with the separately trusted controller API. Missing DB files are not created.

`inspect`, `lookup` and `resolve` do not mutate logical registry state or issue CAS.
Opening SQLite may affect connection/OS bookkeeping; service reads can create remote
access logs. This is not a promise of filesystem byte identity or zero network effects.

`submit-files` validates files before registering the transaction, then invokes existing
registration and commit separately. Pre-registration read/decode/limit refusals leave no
own registry mutations. An isolated test can compare the entire logical DB; concurrent
legitimate activity must be accounted for separately. A cryptographic rejection after
registration can legitimately persist ABORTED with challenge still ISSUED.

## Output and failure meaning

Reports have schema `anchored-store-cli/v1`, operation, `protection="anchored"`,
`authorization="blocked"`, `external_service_qualified=false` and one of:

- `status="completed"`, `result=...`: exit 0, containing the unchanged underlying API
  result. **Completed is not accepted**: examine the redemption/resolution/lookup result.
  A validly processed negative signature can return a rejected redemption and ABORTED.
- `status="error"`, `error=CODE`: exit 2, with stable classification and no nested
  exception text, credential paths or key material. It does not assert transaction rollback,
  ABORTED, non-commit or unchanged remote state.

Argument syntax errors also exit 2, through argparse on stderr. Successful output includes
deployment/revision/store IDs and exact config digest. `inspect` and other result payloads
contain registry data; keep stdout under the same access/audit policy as the registry.
The protection field names the selected adapter, not evidence that an invalid request
reached the checkpoint gate or that any operation succeeded.
The fixed outer authorization field does not establish a new Lean theorem about this CLI.

Witness failures, Prepared, missing slots, mismatched checkpoints and uncertain CAS
propagate as refusals. In particular, lost acknowledgement may hide durable external or
local state. Do not blindly resubmit or infer ABORTED from the exit code. Consult the
existing [anchor recovery protocol](ANCHOR.md) using an authorized operator; resolve
also remains guarded and can itself refuse while the anchor is Prepared. No reset is
performed here. Same-tx retries retain the original outcome; new-tx historical retries
use the existing artifact re-binding rules and journal semantics.

## Deployment boundary

All protected writers must use AnchoredStore. This CLI does not revoke filesystem
access, prevent a trusted owner from running the old CLI/direct SQL, or add service-layer
client authentication around the host process. POSIX/credential trust assumptions and
configuration rollback limits remain as documented in WITNESS_OPERATIONS.md.

Tests use real subprocesses, local temporary PKI and the loopback test witness. This does
not establish production durability/freshness/linearizability or independent rollback
protection. No actual external endpoint is connected. Local SQLite runtime qualification
and the parallel WAL/backport/refinement work remain separate; this batch changes none
of their profiles or system libraries. No new formal proof, physical test or public release
is claimed. Authorization remains blocked, C0–C6 indeterminate, Third Obligation OPEN.

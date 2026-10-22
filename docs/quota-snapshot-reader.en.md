# Bounded QuotaCursorSnapshot v1 file reader

The [reader source](../tools/quota_snapshot_reader.lean) is an executable IO adapter
for the [v1 codec](quota-codec-v1.en.md), not a new formal runtime theorem.

```sh
lake build Verification.CryptoHiddenScalarQuotaCodecContract
lake env lean --run tools/quota_snapshot_reader.lean snapshot.qcs 1048576 10000 1024
```

The four required arguments are FILE MAX_BYTES MAX_BOUND MAX_ROWS. Natural values
use at most 20 decimal digits. The CLI allows MAX_BYTES from zero through 64 MiB;
this application policy does not change v1 or Fits. The `readSnapshotFile` API
accepts arbitrary FitsLimits; callers remain responsible for appropriate limits.

One JSON line is written to stdout. Success reports status=decoded, bytes_read,
bound, row_length, mathematical_restoration=not_run, provenance=not_verified and
authorization=blocked. It means strictDecode succeeded, not that a valid cursor
was restored. The CLI omits row contents; LoadedSnapshot retains them in the API.
Exit 0 means decoded; exit 2 means refusal. Refusal statuses are resource_limit,
invalid_input, io_error, invalid_arguments, invalid_limits, read_contract_violation
and read_budget_exhausted. Wrong argument count reports usage to stderr and exits 2.

## Read protocol

Open read-only without trusting file size. With remaining budget R, request
min(65536, R+1) bytes. An empty response means EOF; a short nonempty response does
not. Reject responses larger than the request, or larger than R without appending
them. Otherwise append and subtract their actual length. At an exact size limit,
probe one more byte to distinguish EOF from excess data. Calls are additionally
bounded by MAX_BYTES+1; exhaustion of that guard is refusal.

Assuming the Handle.read contract, at most MAX_BYTES+1 bytes are returned and each
request is at most 64 KiB. This is tested code behavior, not a theorem about the OS.
Only after EOF is the accumulated ByteArray passed directly to strictDecode.
The file is not reopened. A read exception after a complete frame still refuses.
No profile, key, expected context or mathematical restoration is inferred from the file.

Six live tests include real temporary files and 45 injected-source scenarios.
They cover short reads, EOF, limits 0/65535/65536/65537, excess data, exceptions,
oversized callback replies, OS errors and exact decoder forwarding. A fixed frame
is independently specified by a hexadecimal literal. The source file is preserved.

## Limits

Handle lifetime relies on Lean runtime reference management. Process crashes,
stdout errors and finalizer errors do not guarantee a JSON response. No timeout
is provided: special files and filesystem operations may block. Untrusted use
needs external isolation and timeouts. Byte accumulation bounds do not bound all
allocations, arithmetic, compiler work or OS buffering, and callback checks cannot
undo allocations already performed by that callback.

The source must be stable externally. The reader does not authenticate paths,
symlinks, concurrent writes or appends after observed EOF. Reading can update atime.
Profile file IO, authenticated origin and atomic snapshot writing are separate tasks.

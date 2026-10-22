# Bounded QCP/01 profile reader

The pure [profile codec](../knowledge/04_cryptography/CryptoHiddenScalarQuotaProfileCodecContract.md)
accepts canonical finite rational coefficient lists. Its independent expected-context
API and cursor restoration remain separate from filesystem decoding.

```sh
lake env lean --run tools/quota_profile_reader.lean FILE MAX_BYTES MAX_COEFFICIENTS
```

The CLI opens FILE read-only, requests chunks of at most 64 KiB, and accumulates
bytes up to MAX_BYTES. A one-byte over-limit probe distinguishes exact-sized input
from oversized input. Short nonempty reads continue; only an empty read means EOF.
The strict decoder receives one complete ByteArray after EOF, never a second read.
The CLI caps MAX_BYTES at 64 MiB. The pure codec permits arbitrary supplied limits.

Success prints JSON with status=decoded, format=QCP/01, bytes_read and
coefficient_count. It leaves expected_context=not_checked,
mathematical_restoration=not_run, provenance=not_verified and authorization=blocked.
Exit status is 0 for decoded input and 2 for argument, I/O, limit or format errors.
The separate readExpectedProfileFile/readExpectedProfileWith APIs compare the list
against independently supplied n and expected; the file cannot choose that context.

Injected-source tests cover EOF, short reads, exact caps, oversized reads, read
exceptions, truncated/noncanonical data and context disagreement. File and CLI tests
cover missing files, invalid limits and canonical input. These are bounded tests,
not a formal model of the filesystem. Input limits do not prove bounds on total
RAM, rational arithmetic, runtime, filesystem latency or crash durability. No
snapshot consistency, digital/physical provenance or signature verification follows.
EOF does not prevent concurrent filesystem modification during reading.

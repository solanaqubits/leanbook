# Fixed synthetic four-file vectors

Replay inputs are in `vectors/`. `manifest.json` fixes each file's size/hash.
`good` and `unicode` contain raw QPM/01, detached signature, snapshot/profile bytes
and independently stated expected fields/context/report/message. `cases.json` defines
13 negative vectors including malformed frame/canonicality, signature/artifact mutation,
three independent external-context mismatches and an unissued challenge.
`expected_sql.json` gives all four logical tables before/after the reference transactions,
with explicit BLOB hex values. Tests do not derive expected outcomes from the adapter.

`generate_vectors.py` is optional, exclusive-create tooling, never run by replay tests.
It uses an independent Python encoder and cryptography/OpenSSL signing with the
published RFC8032 test1 seed. No production secret is present. Regenerate into a new
directory and review changes; never bless changed fixtures merely because a test fails.

These artifacts are synthetic hash-binding inputs, not claims of a mathematically
valid QCS/QCP packet or physical measurements. `authorization` remains blocked.

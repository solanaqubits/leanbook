# Native provenance IO adapter

This bounded runtime layer executes the explicit request plan from
`DigitalProvenanceReportContract` (epsilon258). Existing formal modules, their pure
CryptoBackend, registry and sequential replay APIs are unchanged. No new epsilon
or formal cryptographic theorem is introduced.

## Qualified profile and launch

The supplied profile pins Linux x86-64 libsodium1.0.18, Ubuntu package
`1.0.18-1ubuntu0.24.04.1`, exact path and SHA-256 in `profile.json`.
It qualifies this tested artifact, not all releases with that version string.
Replacing/upgrading the binary requires an explicit new profile and conformance run;
no dependency is downloaded or installed automatically.

```
python3 tools/provenance_native/build.py
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest -v tests.test_provenance_native
python3 tools/provenance_native/run.py tests/lean/provenance_native_integration.lean tests/data/provenance_native/integration.json
```

`run.py` executes a trusted local Lean client, not an untrusted-script sandbox. It
checks the binary digest before launch and passes the external path/version to the
client. NativeConfig/Config is externally supplied, never inferred from a signed
package. Direct users of `nativeBackend config` must establish the same binary
qualification independently. Hash-before-open is not a race-safe or adversarial
filesystem guarantee; trusted local files and loader dependencies are assumptions.

The build uses Lean's generated extern wrappers and generated prototypes to check
the C ABI, including the current compiler's erased IO world token. The Raw/Adapter
modules live under tools and are not imported by Verification. No `unsafe` escape
converts IO into a pure callback. Shared Mathlib and Lean dependencies are unchanged.

## Runtime semantics

`IOBackend` exposes SHA-256 and detached PureEd25519 calls in IO. `nativeBackend`
maps native controlled failures to `CryptoError.backend_failure`. Public key length
must be32 bytes, signature64. C rechecks those lengths before reading buffers.
An invalid signature returns `.ok false`; native return0 means valid, -1 invalid,
other codes failure. Loading an absolute library, required symbols, version,
ABI sizes and sodium_init are checked; unavailable/mismatched values fail closed.
Hash results must contain exactly32 bytes before constructing Digest256.

The adapter calls `crypto_sign_verify_detached` directly on the message bytes.
There is no Ed25519ph, external prehash, context wrapper or signing function.
libsodium's strict detached verification policy is pinned and tested for
noncanonical S, noncanonical/invalid point encodings and small-order encodings.
Tests do not establish rejection of every malformed encoding or equivalence with
all other Ed25519 verification policies. No main-subgroup guarantee is inferred
from an auxiliary point-validation API; that API is not used here.

`verifyProvenanceIO` calls pure `prepareVerification` first. A limit error returns
without any backend request. Successful preflight interprets the signature request,
then snapshot/profile hashes, retaining independent refusal statuses. An artifact
size mismatch suppresses its hash call. Revoked/missing keys and malformed signatures
suppress signature calls. `Except.ok Execution` means a report was produced, not
that all stages accepted. Authorization remains the sole blocked constructor.

Execution records requests and observed answers. `responseModel` is an explicit
finite pure model of those answers; it never performs FFI. `conforms` checks exact
requests, answer consistency (including identical hash requests), and equality of
the IO report with pure executePlan. It is a diagnostic/composition conformance
check, not proof of cryptographic correctness or a runtime permission gate.
The integration tests independently instrument actual IO calls as well as checking
this finite model. A fault fixture demonstrates that inconsistent answers for the
same input cannot be explained by a pure backend, even if report statuses coincide.

## Evidence and limitations

Tests replay all5 PureEd25519 vectors from RFC8032 section7.1 and2 NIST SHA-256
examples. Other vectors cover byte mutations, block boundaries, lengths, scalar
malleability, curve encodings, library/version/symbol/init/ABI failures and wrong
native return codes. Negative C libraries are deliberately non-cryptographic fault
fixtures, not production backends. Full-report integration uses a fixed public
RFC test key and a stored signature generated independently with cryptography/OpenSSL;
the test run does not regenerate signatures. The generator is optional and records
its software versions. No fixture key is suitable for real trust.

These are finite conformance tests, not formal C verification, cryptographic-strength
proofs or side-channel audits. IO exceptions and detectable failures are handled;
segfaults, memory corruption, nontermination and fatal runtime allocation failures
may terminate or hang the process. No general memory/time bound is asserted.
No real clock qualification, trust provisioning, physical provenance, atomic/durable
challenge consumption, mathematical cursor restoration or hardware authorization
is supplied. Third Obligation OPEN. Historical Lean proofs remain relative to the
abstract backend; no automatic refinement to machine execution is claimed.

Primary references:
- [libsodium detached signatures](https://doc.libsodium.org/public-key_cryptography/public-key_signatures)
- [libsodium1.0.18 verification source](https://github.com/jedisct1/libsodium/blob/1.0.18/src/libsodium/crypto_sign/ed25519/ref10/open.c)
- [RFC8032 section7.1](https://www.rfc-editor.org/rfc/rfc8032#section-7.1)
- [NIST SHA-256 examples](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf)
- [Lean FFI and interpreter](https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/)

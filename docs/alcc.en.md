# ALCC: canonical bytes to a bound polynomial-certificate verdict

The eight AlgebraicCertificate modules implement and specify this pipeline:
canonical ASCII bytes → JSON AST → typed rational sparse polynomials → SHA-256
passport binding → Boolean certificate check. `AlccVerifyMain.lean` exposes it
as an optional executable:

```sh
lake build alcc-verify --wfail
.lake/build/bin/alcc-verify --passport expected-passport.json --certificate certificate.json
```

The expected passport must be independently selected by the caller. Both files
are read as raw bytes. No Python normalization, JSON reserialization, or alternate
verifier runs inside this CLI.

| Exit | JSON verdict | Meaning |
|---|---|---|
| 0 | VERIFIED_SUCCESS | Bound task, residual has zero polynomial denotation |
| 2 | IDENTITY_MISMATCH | Bound task, this certificate has nonzero residual |
| 3 | DECODE_ERROR | Canonical syntax, schema, binding or structural-budget refusal; no mathematical verdict |
| 74 | EXEC_IO_ERROR | File I/O failure, not a decoder result |
| 64 | EXEC_PROTOCOL_ERROR | Invalid CLI arguments |

The stdout object has exactly `protocol_version: ALCC-BRIDGE-VERIFY-1`,
`evidence_kind: compiled_execution`, and `verdict`. The companion
[SimLab runner and archive auditor](https://github.com/solanaqubits/simlab/blob/main/docs/alcc.en.md)
create byte snapshots, apply process limits, validate this protocol and preserve
receipts. The native Boolean computation relies on compiler/runtime/OS correctness;
it is not a new per-input proof term checked by the Lean kernel.

## Formal result and limits

`verifyCertificateBytes` returns `Option Bool`. Its three main theorems establish
exact equivalence of `none` to `decodeBoundTask = none`, soundness of `some true`
for zero residual denotation, and soundness of `some false` for nonzero residual
denotation. The negative theorem relies on normalization completeness. A bad
certificate does not refute the target implication and does not produce a point
counterexample. Completeness of the whole byte ingestion path is not claimed.

The SHA-256 implementation refines an explicit functional model manually
transcribed from FIPS 180-4; ten test vectors provide concrete controls. This is
not NIST/CAVP certification or a proof of collision resistance. The expected
passport's authenticity, external Python code and physical resource bounds remain
outside the formal result. An independently defined expected input is essential.

The public release adds all eight modules and the CLI; Kernel and Completeness
suites are registered in ProofDAGFullSuite, and the full byte pipeline is imported
by MasterSuite. The new named batch is `proof-graphs/alcc-byte-verification`.
Existing proof contracts and the toolchain are unchanged. The public build-configuration change requires a beta validation checkpoint;
the full gate is run in addition to the affected checks below.

## Reproduce the affected checks

```sh
python3 tools/verifier_skill.py verify Verification/AlgebraicCertificateVerify.lean
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest \
  tests.test_alcc_syntax tests.test_alcc_schema tests.test_alcc_unbound \
  tests.test_alcc_bound tests.test_alcc_verify -v
lake build alcc-verify Verification.MasterSuite Verification.MasterSuiteComponents --wfail
python3 scripts/check_knowledge.py
```

The tests include reproducible byte fixtures, successful reductions and deliberately
false proof attempts that must fail. Tests do not prove the Python fixture generator
correct. Public validation uses the final exported sources; private logs, local
artifact paths and private Git history are not part of this distribution.

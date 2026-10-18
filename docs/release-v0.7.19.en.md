# v0.7.19 — Hidden inner-product compression

This scoped release exports epsilon214,
`Verification.CryptoHiddenScalarInnerProductCompressionContract`, from source
snapshot `037da064d49eae33be383b096aa6aa554cc6493e`.
The registry has 214 direct MasterSuite imports and 258 formal Lean sources,
including Verification.lean. All 258 match the source snapshot byte for byte.

## Results and assumptions

`compress_complete` establishes single-path verification for the computed IPA
context Qe=A+eP, Ueta=eta U, Pipa=Qe+t Ueta and the scalar equation
`t B + z J = T0 + e T1 + e^2 V`. The outer challenge may be zero.
`compression_prefix` and `prover_prefix_causal` establish the message order:
t,z before eta, and L,R before the corresponding internal challenge.

`honest_execution_eq_postprocessing` equates the sequential independent-challenge
execution with the full protocol followed by compression. `compressed_hvzk`
preserves exact transcript-distribution equality for any common compression law;
`execution_hvzk` specializes to the operational law. HVZK assumes bijectivity of
x -> x J. The executable simulator does not invert discrete logarithms and the
compression function uses only the full response and public parameters.

`compressed_extraction_soundness` consumes three pairs of accepting IPA trees
with common outer announcements, distinct outer calls and the prescribed inner
contexts. It composes epsilon211, epsilon212's relation lift, and epsilon213's
three-point extraction. The result is a joint witness opening P and V with the
same inner product, or an explicit nonzero generator relation. No bijective
blinding or hardness assumption is needed for algebraic extraction.

The six trees contain 6*4^k leaves and are supplied extractor inputs, not the
transmitted proof. `compressed_payload` counts 2k+3 prover group elements and four
prover scalars, excluding verifier calls and public parameters. It is not a byte,
operation or execution-time bound. Context rejection follows failed checked
predicates, not arbitrary syntactic changes.

## Validation scope

Public verification is epsilon/scoped for cryptography/bulletproofs-ipa:
strict Lake build, live unittest, one union transitive declaration audit including
strict AxiomAudit, knowledge/catalog and whitespace checks. Private verification
receipts are not reused to certify the public tree. Allowed axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`.

Regression coverage includes honest depths 0,1,2 over F11, internal and external
relation branches, zero outer challenge, prefix causality, computed-context
checks and the executable simulator. Targeted files contain 43 Lean examples,
four helper theorems and 42 runtime scenarios.

Lake remains 0.7.1. The last full public beta basis remains
`2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1); no new full beta run is claimed.

Acquiring fork trees from an adaptive adversary, knowledge-error bounds,
malicious-verifier ZK, Fiat-Shamir/ROM, DLog hardness reductions and formal
polynomial-time guarantees remain open. Public P is not claimed hiding.
Mathematical novelty is not-assessed. Only English documentation and allowlisted
module/integration/test metadata are exported; private materials are excluded.

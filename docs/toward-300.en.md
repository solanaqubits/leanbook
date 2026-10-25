# Extension to 300 direct MasterSuite imports

The counting convention is the number of direct `import` declarations in
`Verification/MasterSuite.lean`. It is not an epsilon identifier, a count of
independent security theorems, or the number of every support file. The public
v0.8.0 source baseline, commit `7f68d8e577136ba3729643e4a57ad740a668670d`,
has 287 such imports. This extension adds 13, for 300; total Lean sources,
including `Verification.lean`, increase from 336 to 349.

The old 81-import backlog is historical. Raft, Multi-Paxos, typed BLS groups,
Shamir finite-field secrecy and kinked interest rates already existed. Their
presence is not counted as new work here.

| New module | Added contract |
|---|---|
| CryptoFeldmanVSSGroup | Arbitrary-degree group commitments determine a consistent polynomial and verified shares reconstruct it. |
| CryptoPedersenVSSGroup | Polynomial share equations, commitment reconstruction and joint uniform hiding of coefficient commitments. |
| CryptoShamirShareRepair | Recover a destination share from a sufficient set, with verified-source and quorum-independence results. |
| CryptoShamirRefresh | Zero-constant refresh preserves the secret and uniformly rerandomizes the whole polynomial fiber. |
| CryptoThresholdBLSGroup | Checked partial signatures reconstruct one signature independently of the sufficient subset. |
| CryptoQualifiedDealerSharing | Agreed qualified-dealer aggregation preserves degree, share consistency and secret reconstruction. |
| CryptoKZGOpeningEquation | Typed opening completeness, fixed-witness uniqueness and explicit exposed-trapdoor failure boundary. |
| CryptoGroth16PairingEquation | Distinct-source-group verification equation and its exact scalar semantics. |
| DeFiAMMExactOutput | Inverse quote, minimal input and exact-input uniqueness in the real model. |
| DeFiAMMIntegerSwap | Exact rounding interval, dust criterion and natural-number reserve-product preservation. |
| DeFiStatefulAMMRouting | Reserve updates across repeated/reverse hops, per-pool product invariant and untouched-pool frame. |
| DeFiFiniteRouteSelection | Maximum quote over a supplied candidate list and minimum-output execution contract. |
| DeFiLendingUtilizationTransitions | Borrow/repay asset conservation, exact utilization changes and rate monotonicity. |

Each module has its own reviewed scope card in [cryptography](../knowledge/cryptography/README.md)
or [finance](../knowledge/finance/README.md), an integration recipe, a named
verification batch and a concrete regression file. The test drivers are
`tests.test_feldman_group`, `tests.test_toward_300_crypto` and
`tests.test_toward_300_finance`. They check exact values, API applications,
excluded-domain counterexamples and a false-share compilation rejection.

The finite field ZMod 7 and scalar pairing models are satisfiability witnesses,
not secure deployed curves. No full VSS/DKG network protocol, computational
hardness, SNARK knowledge soundness or zero-knowledge game is added. Numeric
AMM routes require compatible asset units from the caller; no deployed contract,
concurrent execution or machine-overflow equivalence is asserted. The cards
state the remaining assumptions separately for every module.

This crosses two catalog directions, so the required final gate is beta:
strict build, whole-project verification and transitive axiom audit, the pinned
independent auditor, all live tests, catalog checks and source consistency.
A candidate source count alone does not establish that gate. Exact command
results and hashes belong to the accompanying external evidence archive;
publication and remote CI are reported separately. Historical releases and
private ALCC proof-mode branches are unchanged by these source additions.

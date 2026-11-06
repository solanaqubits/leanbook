# Quantum v4.21: correlated joint inputs

This additive candidate is based on Leanbook v1.0.0, commit
`5276529c6c1010722cc96c39217892b9e874f6a8`. It adds two modules and does not
replace the published tag or its frozen release inventory.

## Instrument

`QuantumCorrelatedMemoryBSM` reduces the existing `QuantumMemoryBSM` joint
instrument by a final environment trace. Direct rectangular operators use
`select * jointBranch`, without an input preparation operator. A dimension-generic
ancilla definition and weighted operator-sum theorem establish complete positivity;
linearity is recorded independently as `reducedJointLinear`. PSD preservation and
zero-trace/zero-output equivalence hold for every joint input satisfying PSD.
The total trace theorem retains the explicit ideal-analyzer matrix hypothesis.
The product-state bridge reuses v4.20, and linearity extends it to finite sums.
Complex coefficients are allowed algebraically; interpreting such a sum as a
physical separable mixture additionally requires nonnegative normalized weights
and physical component states. Separability is not a zero-discord assertion.

## Fixed-interaction witness

`QuantumCorrelatedMemoryWitness` constructs two PSD trace-one densities with the
same system marginal AND the same environment marginal. The environment-controlled
X on B precedes the ideal Bell analyzer. Both inputs give probability 1/4 to each
reported branch, but the corrected outputs are respectively Phi+ and Psi+.
Accepted target overlaps are exactly 1 and 0. The contradiction excludes ANY
function of the system marginal for this fixed configuration on all physical
joint inputs. It does not exclude reduced channels for other interactions.

The proposed `memoryStages E F` placement needed correction: its E follows CNOT,
rather than preceding it. The witness prepends a separate identity-gate/noise
stage; `witness_ideal` and `witness_effective` prove the resulting circuit facts.
The optional GHZ witness with different branch probabilities is not part of this
candidate. No probability difference is inferred from unequal output matrices.

## Validation

[Verification record](quantum-v4.21-verification.json) and
[theorem inventory](quantum-v4.21-inventory.json) bind the checked sources by SHA-256.
Strict incremental `lake build --wfail` passed (4122 jobs, two freshly built targets
at that final build step). `verify-all` re-elaborated 382 checked roots and audited
42,725 declarations; the pinned independent auditor agreed. Only `propext`,
`Classical.choice`, and `Quot.sound` occur, with no violations or sorryAx.
These declaration counts include helpers and are not independent research results.

All 674 distinct tests have successful observations, with zero skips or unresolved
failures. The complete discovery run passed 671 and encountered three environment
contract failures in clean-build tests. After correcting the container swap limit,
all 12 tests in that affected module passed. This is a full run plus targeted
recovery, not a claim of a single clean full run. An earlier host discovery attempt
was interrupted because the pinned SQLite runtime was absent; its log is retained.
No tests, assertions, proof checks or source code were weakened for recovery.

The synchronization archive includes the actual CLI logs, failure history, source
fingerprints, 67 exported declaration signatures with axiom dependencies, and a
per-test reconciliation against all 674 discovered identifiers. Published v1.0.0
results are not counted as fresh checks of this candidate.

## Boundaries

Theorems concern finite-dimensional matrices and a single measurement/correction
cycle. Adaptive process tensors, general Pechukas–Alicki assignment-map results,
physical relaxation times and hardware characterization remain outside scope.
The concrete witness uses a two-dimensional environment; the instrument accepts
an arbitrary finite environment and arbitrary joint PSD inputs.
Novelty is not assessed.

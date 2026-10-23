# Bounded public synchronization of Prometheus proofs

This synchronization exports nine previously private modules and their selected
regressions, English knowledge cards and registry fields. The starting public
revision is `2939f0c672e181be11c6ccbe8001f517452b0c8c`. Exact source hashes and
the private source revision (a provenance identifier, not a public source link)
are recorded in [the export manifest](prometheus-lean-export.json).

All nine module files are byte-identical to the pinned private source. Their
five existing project dependencies are unchanged and byte-identical as well.
The public verifier, toolchain, runtime, conformance mechanism and existing
proof-source files are preserved; only the integration roots add suite wiring.
Other private streams are not exported. The existing full beta basis is retained.

## Scope and limits

| Modules | Mathematical content | Unproved bridge |
|---|---|---|
| PrometheusVariableQueue / PrometheusLifetimeInformation | Variable-input accounting, finite-law score information and conditional metrology bounds | Empirical timings are not WCET; emitted energy does not specify timestamp precision |
| PrometheusCascadedFECBound | Specified rep5/byte probabilities and conditional IID Chernoff tail bound | No implementation PER certificate; no automatic transfer to correlated traces |
| PrometheusMultiLaneQueue / PrometheusLifetimeIdentifiability | Round-robin bounds including equality; overload for constant service; calibrated two-channel identifiability | Unknown beta efficiency is confounded; no hardware capacity or universal sensitivity limit |
| PrometheusJitterWindow / PrometheusRSCycleModel | Common-mode cancellation, conditional probability bounds and fixed 2960-cycle controller | No measured device jitter, general algebraic decoder refinement or physical WCET |
| PrometheusNQKDFiniteKey | Scalar floor/budget equivalence and explicit abort guards | No unconditional finite-key quantum security proof or authenticated physical key release |
| PrometheusThresholdTomography | Threshold-function counterexamples and linear sensitivity rank/kernel results | No continuous optimum, universal tomography impossibility or physical apparatus certificate |

These are conditional mathematical results. Full theorem types and knowledge cards
remain authoritative for their exact hypotheses. A source filename or successful
axiom audit does not establish applicability to a proposed device.

## Verification and reproduction

The public-tree plan is bounded (`delta`, with the changed members of six
Prometheus batches and affected integration consumers). Explicit selection covers
all public Prometheus regression suites plus catalog and verification-scope tests.
The planner selects a strict registry/root build and a fresh transitive axiom
check rooted at `Verification.AxiomAudit`. Overlapping imported declarations are
counted once in that check, not summed across historical stages.

This is not a new full beta checkpoint or the later independent system audit.
Final results and selected commands are recorded in
[the public verification receipt](prometheus-lean-checks.json).
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The historical SimLab metadata supplement is pinned at
[`75ff1d3e811cddeab8ec9b15966e8d5d6e78d8cb`](https://github.com/solanaqubits/simlab/tree/75ff1d3e811cddeab8ec9b15966e8d5d6e78d8cb/studies/prometheus_program).
It reports previous numerical results; this Lean publication does not rerun them.
No grant application, raw private journal or private Git history is exported.
Physical realizability, certified positive secret-key rate, hardware WCET and
the Third Obligation remain **OPEN**. Hardware admission and authorization are unchanged.

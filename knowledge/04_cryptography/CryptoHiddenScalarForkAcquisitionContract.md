---
id: CryptoHiddenScalarForkAcquisitionContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarForkAcquisitionContract.lean
novelty: not-assessed
status: reviewed
---

# Snapshot-indexed acquisition of nested hidden-scalar forks

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarForkAcquisitionContract.lean)

## Model and executable acquisition

`AdversaryModel` fixes one tape, initial memory and a deterministic, total step
function. A step may return `none`, representing an abort within the model.
Snapshots contain tape position, challenge history and local memory. `advance`
increments position by the reported nonnegative amount and appends the request.
`ReachableSnapshot` records actual transition equations. Restoring a reachable
snapshot is its exact saved value; this is a model definition, not an operating
system rollback theorem. `Observation.reachable` and `origin_child_reachable`
prove preservation along real model transitions.

`ProbeSchedule` gives each attempt its own lower-level schedule. `acquireTree`
passes the observed child snapshot, rather than identifying states having equal
algebraic statements. `acquireNode` collects two distinct unit eta calls after
one fixed e response, and `acquireCompressedFork` collects three distinct e
branches after the same initial announcement. Internal nodes collect four
nonzero distinct squares. At depth zero eta produces the leaf directly.

The search restores before every candidate and stops at its quota. A duplicate
of a retained successful key is rejected without an adversary query; its restore
is still logged. A previously unsuccessful call may be retried with a different
child schedule. Local exhaustion does not abort the parent loop. Only initial
abort/unexpected initial message and outer exhaustion are terminal errors.

## Provenance, validity and extraction

`TreeOrigin`, `NodeOrigin` and `ForkProvenance` contain equations of observations
from the same tape and exact parent states. Successful values carry proofs
constructed during traversal; the algorithm takes neither accepting trees nor
`ValidCompressedFork` as an input.

`acquire_provenance_and_valid` proves model-relative provenance and the epsilon214
validity predicate. `acquire_and_extract_soundness` applies epsilon214 directly:
a joint witness opening P and V with the required inner product, OR an explicit
nonzero generator relation. The six trees, with 6·4^k leaves, are acquired internal
objects, not a single transmitted proof.

## Resources and conditional probability

Every outcome retains its `ResourceTrace`. Queries, restores, elementary
rejections and exhausted search nodes have separate counters. `tree_trace_bound`,
`node_trace_bound`, `acquisition_trace_bound` and `resource_bounds` give explicit
finite schedule-only bounds, including failed runs. They count model operations,
not CPU time or the work hidden inside the adversary's step function.

`Clean` excludes rejection and exhaustion events. `scan_clean_cost`,
`tree_clean_cost`, `node_clean_cost` and `clean_acquisition_exact` connect the
actual program to exact rejection-free costs. The initial message costs one query;
eta already emits the IPA root. Consequently Q(k)=4+2(4^(k+1)-1) and R(k)=Q(k)-1.
Duplicate/rejected attempts are accounted from the executed log instead.

`traceTests` checks the actual log, padded to a common finite fuel bound.
`trace_tests_clean` and `clean_schedule_probability_lower` derive a success lower
bound equal to the product of explicit sequential conditional bounds on those
tests. Seeds can encode independent product draws or correlated schedules; no
independence is silently assumed. This conservative theorem counts clean schedules;
successful retries can contribute extra probability. `ScanSuccess` and
`AcquisitionSupport` provide a separate operational interface for more general
retry histories, used by `acquisition_probability_lower` with an explicit
realization proof. No density premise is inferred from marginal acceptance.

## Regression and limits

Finite-field regressions exercise depth-zero and multilevel acquisition, witness
and relation extraction, duplicate filtering, repeated failed calls with fresh
suffixes, prefix-dependent state, early stopping and retained failure logs.

The algebra uses a prime scalar field and an additive scalar module; executable
checks require decidable equality. There is no new hiding hypothesis. The model
is not automatically a refinement of an external process. Density for an
arbitrary interactive adversary, general Bellare–Neven rewinding bounds, ROM,
Fiat–Shamir and polynomial complexity remain unproved. Previous epsilon208–209
probability recurrences are not reused by equating snapshots with statements.

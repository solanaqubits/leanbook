---
id: PrometheusDecoderQueue
language: en
section: quantum-physics
source: Verification/PrometheusDecoderQueue.lean
novelty: not-assessed
status: reviewed
source_sha256: b3e79f8ba16c7de42f59aade66832d36ac1818e86ba71740bb96f462daccd47e
---

# Deterministic decoder queue and conditional full route budget

[Section](README.md) ·
[Lean](../../Verification/PrometheusDecoderQueue.lean)

Epsilon 250, direction `quantum-physics`, batch `prometheus-decoder-queue`.
This stage-2 result formalizes a deterministic queue. CPU profiling, codec
optimization and finite queue experiments live separately in SimLab; measured
medians are not promoted to Lean hypotheses.

## Model and proved statements

`QueueInput` supplies real arrival and service sequences and initial server
availability. All times use a common unit. A single server processes index order
without preemption or drops: ready(0)=initialAvailable, start(i)=max(arrival(i),
ready(i)), finish(i)=start(i)+service(i), ready(i+1)=finish(i),
waiting(i)=start(i)-arrival(i), sojourn(i)=finish(i)-arrival(i).

Waiting is nonnegative, consecutive services do not overlap, and
sojourn=waiting+service. Nonnegative sojourn also requires nonnegative service.
The Lindley recurrence uses the preceding service index exactly:
waiting(i+1)=max(0,waiting(i)+service(i)-(arrival(i+1)-arrival(i))).
`QueueInput.Valid` separately requires chronological arrivals, nonnegative
service and initialAvailable≤arrival(0). General algebraic identities do not
silently assume validity; arbitrary index sequences need not describe physical
chronological FIFO arrivals.

Exact periodic arrivals with A>0, initial idleness and pointwise
0≤service(i)≤A imply zero waiting at every index. A median or mean is not this
pointwise condition. For constant s≥A, waiting(i)=i*(s-A). Strict overload s>A
implies strict growth and an index above every real waiting threshold in the
infinite extension. The general formula is algebraic;
`positive_period_overload` adds A>0 and supplies Valid together with the
unboundedness conclusion. This is not a finite-buffer guarantee or an observation
about a finite experiment; dropping on overflow is outside this model.

## Exact serialization and counterexamples

Serialization is n*slot. Examples use milliseconds: 10ns=1/100000ms and
9600 slots=0.096ms=96us. Constant 1ms service with 96us arrivals yields waiting
0.904ms at index1 and 1.808ms at index2. Every service is≤1ms, stronger than a
median bound, yet the queue grows. These are stipulated constants, not measured
CPU timings. Regression counterexamples exhibit initial backlog, simultaneous
arrivals and negative service; a [2,0,0,…] service sequence at period1 checks the
recurrence index and draining backlog.

## Conditional route bound

Route total is encode+serialize+propagate+wait+service+extra. `packetBudget`
links actual queue-model waiting/service and serialization to this budget.
Nonnegative terms and componentwise supplied caps prove a total upper bound and
a saving lower bound relative to a supplied reference. Extra covers other costs
only when independently bounded.

An explicit example caps encode at1ms, serialization at0.096ms, propagation at
40.410ms, wait at0, service at1ms and extra at0. With nonnegative components,
total≤42.506ms and saving≥35.415ms relative to77.921ms. Propagation values are
rounded inputs. Zero waiting/extra do not follow from the 1ms service cap.
This example is neither measured data nor a codec runtime or96us stream guarantee.
A positive unconstrained extra can erase the advantage; a regression witnesses it.

## Evidence and limitations

Historical development evidence, pinned by the source SHA256 above: standard verify
passed115 declarations with only propext/Classical.choice/Quot.sound and no
violations. Two live tests passed without skips:44 regression examples and6 registry examples.
Strict affected-registry/root build passed3934 Lake jobs with294 fresh project
targets in the new worktree; Mathlib used the shared cache. The registry field
`QuantumPhysicsFullSuite.prometheus_queue` is checked;
actual commands/results are retained in prometheus-decoder-queue-250-evidence/lean-dev.
This is scoped epsilon evidence, not a new full beta gate. No direct Verification
imports. Novelty has not been assessed.

Entry points: lindley_recurrence, periodic_zero_waiting, constant_overload_waiting,
positive_period_overload, frame_serialization_exact, one_ms_service_counterexample,
packet_total_eq, route_total_upper_bound and conditional_example_saving.

No OS/scheduler refinement, CPU WCET, implementation throughput, finite-buffer
correctness, stochastic stability or physical qualification is proved. Hardware
authorization and the Third Obligation are unchanged.

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).

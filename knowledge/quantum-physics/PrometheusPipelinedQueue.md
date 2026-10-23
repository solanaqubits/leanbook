---
id: PrometheusPipelinedQueue
language: en
section: quantum-physics
source: Verification/PrometheusPipelinedQueue.lean
novelty: not-assessed
status: reviewed
source_sha256: daa81227d22499bef88861a5d87fafd6bae2794aa948c9a551e7030e8785fb81
---

# Parallel FIFO lanes and finite waiting-buffer bounds

[Section](README.md) · [Lean](../../Verification/PrometheusPipelinedQueue.lean)

Epsilon253, quantum-physics/prometheus-pipeline-metrology. This extends epsilon250's
single-server queue by reuse, preserving its source and API. The requested
parallel-decoder filename is represented by the project-style module name above.

## Exact contract

Each lane is an existing QueueInput, with ready(0)=initialAvailable,
start(i)=max(arrival(i),ready(i)), finish(i)=start(i)+service(i), and
ready(i+1)=finish(i). Services are nonpreemptive, in FIFO index order. Parallel
lanes are static cyclic destinations, not a shared work-conserving dispatcher.
P>0 is explicit in physical pool contracts.

LaneEnvelope assumes chronological arrivals, A>0, J>=0, an initially idle lane,
0<=service(i)<=S<=A, and e+i*A<=arrival(i)<=e+i*A+J for every i. This is a
bounded-jitter deterministic envelope, not a measured WCET or stochastic stability
claim. Induction on the actual recurrence derives start(i)<=e+i*A+J; consequently
waiting(i)<=J and sojourn(i)<=J+S. No queue-bound conclusion is assumed.

waitingSet(horizon,t) contains indices i<horizon with arrival(i)<=t<start(i).
It includes waiting arrivals and excludes packets in service, including the
boundary t=start(i). If J<=b*A for a natural b, every such set has cardinality<=b.
The proof places all its members in [minIndex,minIndex+b). Summing over P lanes
gives poolWaiting<=P*b. Thus a waiting-only buffer B>=P*b has bufferOverflow=false
for every finite horizon/time, including simultaneous arrivals. This establishes
capacity feasibility of the explicit no-drop schedule. Admission/drop state-machine
refinement, shared-buffer routing and arbitrary burst envelopes are not proved.

For periodic global arrivals separated by dt, cyclic lane l receives index P*i+l;
its lane period is P*dt. With S<=P*dt it has zero waiting. One packet's service is
still S, never S/P. A concrete P=20,dt=.2ms,S=4ms witness satisfies the premises.
A regression also instantiates J=.2ms,b=1,B=20 as a conservative buffer certificate.

## Deadline and counterexample

routeLatency=propagation+serialization+waiting+service. Explicit upper bounds
propagation<=40.411ms, serialization<=.2ms, J<=.2ms and S<=4ms give total<=44.811ms,
hence total<45ms and total<77.921ms. The theorem uses the propagation premise;
it does not prove spherical geometry. The separately named propagationMs=40.410046
is a nominal rounded rational, not an exact geometric constant. Acquisition,
encoding and other overheads are omitted and must be budgeted separately.

The full service lower bound6.234ms already implies nominal latency>45ms when
serialization>=0. Even P=65 lanes can have zero waiting at dt=.096ms and still
miss45ms. The exact comparison64*.096<6.234<=65*.096 separates throughput from
per-packet latency. The6.234ms number is a stipulated bound in these theorems,
not a conversion of an observed median into a WCET or lower bound on every run.

## Verification and scope

Standard verify passed: 168 declarations in the transitive project closure,
only propext, Classical.choice and Quot.sound, no violations. Both integrations
passed; final registry closure34740 declarations and root3938 Lake jobs (cached
targets included). Seven live unittest methods passed without skips, including
three new methods with70 Lean examples (24 queue,40 metrology,6 registry).
Closure declaration counts overlap and must not be summed.

Key declarations: start_upper, [waiting_card_bound](../../Verification/PrometheusPipelinedQueue.lean#L77), pool_waiting_bound,
[finite_buffer_no_overflow](../../Verification/PrometheusPipelinedQueue.lean#L118), cyclic_zero_waiting, [conditional_45ms](../../Verification/PrometheusPipelinedQueue.lean#L172),
conditional_fiber_advantage, twenty_lane_example, [six_ms_service_obstruction](../../Verification/PrometheusPipelinedQueue.lean#L199).
Registry field: QuantumPhysicsFullSuite.prometheus_pipeline. Direct project import:
Verification.PrometheusDecoderQueue. Novelty not assessed. No hardware qualification,
authorization change or Third Obligation status change follows. Logs and original
failures are retained in prometheus-pipeline-253-evidence/lean-dev. Final main
reconciliation belongs to the parent integrator; no new beta checkpoint is claimed.

Independent public validation for this source is recorded in [release v0.7.46](../../docs/release-v0.7.46.en.md).

---
id: ExternalActuatorContract
language: en
section: distributed
source: Verification/ExternalActuatorContract.lean
source_sha256: 1320dcec575de446f29afacfd0d58125cc1ed4818881dac8287d3482868b040d
novelty: not-assessed
status: reviewed
---

# Actuator command history and crash recovery

[Section](README.md) · [Lean](../../Verification/ExternalActuatorContract.lean)

The model uses an arbitrary Action type and explicit authorization and action-bound
confirmation predicates. Action identity, canonical codecs, cryptography, grant
uniqueness and implementation correspondence are not proved here.

A journal maps every Action to an optional status. Absence is not permission to
forget prior history. A successful reserve transition represents a completed trusted
durable ARMED write and creates one volatile permit. Issue requires ARMED and that
permit, consumes the permit, and retains ARMED. Recovery preserves the journal and
removes all permits. Completion needs an explicit confirmation predicate; lockout
can disable an action even before dispatch. No transition deletes an occupied ID,
reserves it again, or restores a spent permit. A failed or incomplete persistence
operation cannot be represented as a successful reserve.

## Proved statements

`step_preserves_history` and `run_preserves_history` retain occupied IDs.
`step_preserves_spent`, `run_preserves_spent` and `recovered_action_stays_disabled`
prevent a spent occupied ID from regaining permission through valid continuations.
`run_budget` proves the trace invariant: dispatch count plus current permit credit
is at most the indicator that the ID is present. Reserve, issue, recovery and lockout
preserve this invariant. `at_most_one_dispatch` consequently bounds each ID's software
command dispatch count by one in every finite valid run from the initial state.
Zero dispatches are allowed; liveness and successful physical effects do not follow.
`implementation_bound` requires an explicit refinement witness from a concrete trace
to this model. No such witness for a database, TPM or driver is supplied.

## Observation ambiguity

The histories reserve/recover and reserve/issue/recover are both reachable under
authorized action identity. Their recovered states agree, but dispatch counts are
zero and one. `observe` exposes the whole durable journal and one explicitly chosen
sensor value. `reachable_indistinguishable_histories` packages these facts;
`no_observation_classifier` rules out a deterministic function of this observation
that correctly classifies both histories. A classifier returning unknown is allowed.
Equal sensor readings are an explicit observation context, not a sensor-physics
result. Additional trusted history is outside this indistinguishability claim.

## Limits

Durable history preservation and exclusive sequential ownership are modeled by
Step/Run. Rollback, cloned live permits, independent concurrent owners and hidden
retries require separate implementation refinement. EXECUTED is a status with an
external confirmation predicate, not a measurement of physical success; lockout does
not prove a safe physical position. Issue denotes one software dispatch, not an
electrical pulse or mechanical effect. No hardware, runtime deployment or arbitration
implementation is certified. Scoped kernel/model regressions are separate from
future external acceptance scenarios. Novelty is not assessed.

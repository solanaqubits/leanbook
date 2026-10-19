# v0.7.26 — Tape averaging and actuator trace contracts

This release exports `CryptoHiddenScalarTapeAverageContract` (epsilon222) and the
separately named `ExternalActuatorContract` from private source
`a40f78b37405d6da1e58f4a462a17a9b47d0d503`.
The registry has 223 direct MasterSuite imports and 267 formal Lean sources.

## Finite tape averaging

A common claim, initial memory and adversary step are shared across tapes. Finite
normalized rational tape weights combine with each tape's original ProtocolPlan
microseed law and decoder; plans and budgets may differ. Conditional acceptance
thresholds guard the lower bound. The expectation bounds actual acquisition success
from below. Strict positivity is equivalent to a positive-weight qualifying tape
with positive computed bound, and yields a successful pair of positive joint mass
with witness-or-generator-relation extraction. No new collector or extractor is used.
This does not prove efficient search, infinite-tape generalization, arbitrary replacement
conditional laws, ROM or polynomial-time extraction.

## Actuator trace contract

A completed durable reserve creates one volatile permit. Issue consumes it while
preserving the full action journal; recovery drops all permits. Valid sequential
traces dispatch each action ID at most once. Two reachable recovered histories can
have equal journal/sensor observations but dispatch counts zero and one. These are
software trace results: no physical exactly-once effect, sensor physics, concrete
persistence/fencing implementation or deployed arbitration is certified.

## Verification scope

The public scoped planner covers both cryptography and distributed directions,
affected integration, their reviewed live tests and one union transitive axiom audit.
Only propext, Classical.choice and Quot.sound are allowed. No native-decide bypass.
This is not a new full beta checkpoint. Lake remains 0.7.1, and the full public beta
basis remains `2419489245019fb16e32ffac641b9f88eea94126` (v0.7.1).
Private SimLab materials, private Russian cards and raw chats are not exported.

[Tape averaging](../knowledge/04_cryptography/CryptoHiddenScalarTapeAverageContract.md) ·
[Actuator model and limits](../knowledge/distributed/ExternalActuatorContract.en.md)

# Quantum v4.26 — two-round adaptive swapping cascade

Local scoped/gamma addition on `f075bb4657382c0f5677326b6853cfbe728d024c`
(v4.24), branch `quantum-cascade-v426`. The v4.25 scope check remains a separately
checked prototype of existing corollaries, not an intervening integrated commit.
Published Leanbook `v1.0.0` is unchanged. No dependency or toolchain update.

[Exact inventory](quantum-v4.26-inventory.json) ·
[Verification record](quantum-v4.26-verification.json)

## Corrected specification

The cascade composes **unnormalized** branch maps. Conditional division is generally
nonlinear and is never used as the map for which complete positivity is claimed.
The first output has dimension 4. A fresh pair, typed `EnvironmentState PairIndex`,
raises it to dimension 16; an independent `EnvironmentState e₂` then supplies the
second-round memory. The first round may have a different environment `e₁`.
The original proposal's generic fresh-pair dimension, shared stage-list types,
extra `some o₂`, stray `r₁` and circular probability identity are not retained.
A zero real trace implies a zero matrix only under the explicit PSD premise.

## Contracts

`KrausBranch` supplies finite rectangular operators, a complex linear map,
ancilla-general CP and PSD proofs. Its composition has operators `L_j K_k`.
`preparation` reuses `prepareOp` and `preparation_semantics`; its trace preservation
follows from the normalized fresh state. `Round.branch_map` proves exact agreement
with `noisyJointOutcome` from v4.24 for rejection and all delivered messages.
Each `Round` stores the inherited analyzer equality needed by five-outcome balance.

`Cascade.second`, `freshPair` and `freshMemory` are indexed by the **delivered**
first message. They are fixed functions of that label; they do not inspect the
hidden first measurement or the input matrix. The first environment is discarded.
`cascade_kraus` explicitly expands the second operator, second-memory preparation,
fresh-pair preparation and first operator in that order. Its input dimension is
16 times dim(e₁), output dimension 4. `continuation_semantics` and `cascade_semantics`
connect this representation to the old instrument maps.

`TerminalOutcome = Option (BellMeasurement × Outcome)` has exactly 21 elements.
`none` stops after first rejection. `some (r, none)` means rejection in round two,
and is distinct from early rejection. There is no second round on early rejection.
Every terminal branch is complex-linear, CP and PSD-preserving; their traces sum
to the initial trace. On a density input the probabilities are nonnegative and sum
to one. The trace identity itself is algebraic and holds for all matrices.

`conditionalContinuation` evaluates the second instrument on `normalizeOrZero`
of the first branch. `cascade_reconstruction` and `cascade_probability_factorization`
prove the actual chain rule, including its zero sentinel extension. For positive
first probability, `conditional_total_trace` proves that the five conditional
second probabilities sum to one. `zero_first_branch_gives_zero_continuation`
uses PSD and annihilates every continuation without dividing by zero.

## Regression and scope

Targeted fixtures include different first/second environment dimensions, a
five-dimensional spectator, complex linearity, conditional normalization, and
registry export. A concrete feedback rule disables second-round detection only
after delivered phiPlus. On the earlier GHZ correlation witness, the first phiPlus
probability 1/2 is routed entirely into **second rejection**; the other witness's
zero first branch has zero continuations. This exercises the distinction between
all 21 terminal paths, not just an all-success instrument.

Validation is scoped/gamma: strict new-module elaboration and imported axiom
closure, incremental root build, targeted container regressions, metadata checks
and an independent compiled-project axiom audit. Actual counts and unsuccessful
attempts are recorded in the verification record. No fresh full verify-all,
full test discovery, clean rebuild or remote CI result is claimed.

## Limits

Two rounds of swapping with fresh resources; no distillation circuit, repeated
coupling to retained quantum memory, arbitrary adaptive process tensor, or hardware
calibration. The environment of round two is initially independent of the supplied
pair and fresh pair within each observed first branch. The instrument includes
classical feed-forward, not coherent control over a hidden outcome. Existing
Werner laws keep their original hypotheses and are not generalized here.

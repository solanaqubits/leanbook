---
id: QuantumCascadedSwapping
language: en
section: quantum-physics
source: Verification/QuantumCascadedSwapping.lean
source_sha256: 7b63a3025a6ccc01334cae528cf557f068d621d1dbecaad7cfe8a5a497b3e20a
novelty: not-assessed
status: reviewed
---

# QuantumCascadedSwapping

[Section](README.md) · [Lean source](../../Verification/QuantumCascadedSwapping.lean) ·
[Scope and verification](../../docs/quantum-v4.26.md)

Two unnormalized swapping rounds with delivered-message feedback. Round one may
start with arbitrary system/environment correlations. Its environment is discarded;
round two receives the output pair, a fixed fresh pair and independent fresh memory.
The second stages, readout, post channel and both resources may depend on the
observed first message, not on its hidden physical outcome or the input matrix.

A finite rectangular Kraus family supplies each branch. Composition multiplies
operators in chronological order, and preparation reuses the square-root Kraus
construction from QuantumMixedEnvironment. Round.branch_map identifies each round
with the checked v4.24 instrument, including post noise and rejection.

TerminalOutcome is Option (BellMeasurement × Outcome), of cardinality 21: early
rejection, or four first messages followed by five second outcomes. All terminal
maps are complex-linear, completely positive for any finite ancilla, and preserve
PSD. Summing their traces gives the input trace, including early rejection.
Each Round explicitly carries the inherited ideal-analyzer premise for trace balance;
its chronological noise and post channels remain arbitrary CPTP channels.

Normalization is separate. The chain rule evaluates the second probability on the
normalized first branch. It also holds algebraically at zero first probability
with the zero sentinel. PSD is required to reconstruct or annihilate a zero-trace
branch. At positive first probability the conditional second outcomes sum to one.

## Theorems

- [`QuantumCascadedSwapping.KrausBranch.cp`](../../Verification/QuantumCascadedSwapping.lean#L40)
- [`QuantumCascadedSwapping.KrausBranch.positive`](../../Verification/QuantumCascadedSwapping.lean#L48)
- [`QuantumCascadedSwapping.KrausBranch.comp_map`](../../Verification/QuantumCascadedSwapping.lean#L61)
- [`QuantumCascadedSwapping.preparation_map`](../../Verification/QuantumCascadedSwapping.lean#L77)
- [`QuantumCascadedSwapping.preparation_trace`](../../Verification/QuantumCascadedSwapping.lean#L81)
- [`QuantumCascadedSwapping.Round.branch_map`](../../Verification/QuantumCascadedSwapping.lean#L107)
- [`QuantumCascadedSwapping.Round.total_trace`](../../Verification/QuantumCascadedSwapping.lean#L123)
- [`QuantumCascadedSwapping.terminal_outcome_card`](../../Verification/QuantumCascadedSwapping.lean#L141)
- [`QuantumCascadedSwapping.continuation_semantics`](../../Verification/QuantumCascadedSwapping.lean#L162)
- [`QuantumCascadedSwapping.cascade_semantics`](../../Verification/QuantumCascadedSwapping.lean#L169)
- [`QuantumCascadedSwapping.cascade_kraus`](../../Verification/QuantumCascadedSwapping.lean#L176)
- [`QuantumCascadedSwapping.terminal_cp`](../../Verification/QuantumCascadedSwapping.lean#L192)
- [`QuantumCascadedSwapping.terminal_positive`](../../Verification/QuantumCascadedSwapping.lean#L195)
- [`QuantumCascadedSwapping.terminal_sum`](../../Verification/QuantumCascadedSwapping.lean#L199)
- [`QuantumCascadedSwapping.continuation_total_trace`](../../Verification/QuantumCascadedSwapping.lean#L206)
- [`QuantumCascadedSwapping.terminal_total_trace`](../../Verification/QuantumCascadedSwapping.lean#L212)
- [`QuantumCascadedSwapping.cascade_reconstruction`](../../Verification/QuantumCascadedSwapping.lean#L225)
- [`QuantumCascadedSwapping.cascade_probability_factorization`](../../Verification/QuantumCascadedSwapping.lean#L238)
- [`QuantumCascadedSwapping.zero_first_branch_gives_zero_continuation`](../../Verification/QuantumCascadedSwapping.lean#L245)
- [`QuantumCascadedSwapping.conditional_total_trace`](../../Verification/QuantumCascadedSwapping.lean#L252)
- [`QuantumCascadedSwapping.terminal_probability_nonnegative`](../../Verification/QuantumCascadedSwapping.lean#L260)
- [`QuantumCascadedSwapping.terminal_probabilities_sum_one`](../../Verification/QuantumCascadedSwapping.lean#L265)
- [`QuantumCascadedSwapping.verification_suite`](../../Verification/QuantumCascadedSwapping.lean#L280)

## Limits

Exactly two swapping rounds with fixed message-dependent fresh resources. No
purification/distillation circuit, retained quantum memory between rounds, arbitrary
adaptive process tensor, or hardware timing/noise calibration is claimed. A change
in conditional fidelity is not assumed monotone under general CPTP post noise.
Counts include helper and registry theorems, not independent scientific results.

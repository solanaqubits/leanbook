---
id: QuantumIVCAccumulatorContract
language: en
section: quantum-physics
source: Verification/QuantumIVCAccumulatorContract.lean
novelty: not-assessed
status: reviewed
source_sha256: 5dd19e3f8e75cbf5c57d2306f74527ea328fc1c2d82f1b8e3164cfc6ed77eab9
---

# Boolean accumulation, declared losses and a cost model

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumIVCAccumulatorContract.lean)

Stage ε275. The name Quantum/IVC does not establish an implemented
cryptographic folding scheme or a physical quantum accumulator.

## State and folding

`StepWitness` stores `stepIndex : ℕ`, `valid : Bool`, `fidelityLoss : ℚ`
and a proof of loss≥0. `IVCAccumulator` stores `totalSteps : ℕ`,
`allValid : Bool`, `accumulatedFidelity : ℚ` with 0≤F≤1.
`emptyAccumulator` is (0,true,1). `foldStep acc w` increments the count,
computes `allValid && valid`, and sets F to `max 0 (F−loss)`.
`foldSteps` applies this transition to a finite list.

The proofs give preserved bounds, nonincreasing F, exact count initial+length,
and final allValid=true iff the initial flag and every list flag are true.
An initial false or any false witness absorbs every suffix. Theorems named
soundness here preserve Boolean values, not cryptographic commitments.

`foldStep_index_independent` proves that changing stepIndex does not affect
the transition. The count therefore checks no index sequence, event uniqueness,
order or replay condition. An arbitrary accumulator can be passed directly
to verification without providing a history that produced it.

## Losses and conditional semantics

`totalLoss` sums nonnegative declared losses. The exact formula is
`F_final = max 0 (F_initial−totalLoss history)`.
For ε≥0 and every loss≤ε, it implies
`F_final ≥ max 0 (F_initial−length·ε)`.
This is a scalar budget without physical fidelity calibration, tomography or
a decoherence law. Neither the quantum name nor registry integration connects
it to NV-centre coherence.

`verifyAccumulator acc Fmin` is `allValid && decide(Fmin≤F)`.
Fmin is an arbitrary rational: Fmin>1 rejects every valid accumulator;
Fmin≤0 makes verification equal allValid, including F=0. The empty accumulator
is accepted exactly when Fmin≤1. Acceptance alone thus establishes neither
positive physical accuracy nor an authentic record.

`conditional_semantic_soundness` concerns a specific `foldSteps acc history`.
Besides acceptance, it needs an external premise for every listed witness:
`w.valid=true → R w`. It then concludes R for each list element. Flags do not
establish that premise. The theorem does not authenticate the initial accumulator
or statements preceding the particular list.

## Explicit expression cost

`VerifierExpr` has `ReadValid`, `FidelityCompare` and `And` nodes.
`evalVerifierExpr` returns Bool×ℕ. Each leaf costs 1; And evaluates both
branches in the model and adds 1.
`verificationExpression = And ReadValid FidelityCompare`.
The exact result/cost correspondence is proved:
`evalVerifierExpr acc Fmin verificationExpression = (verifyAccumulator acc Fmin,3)`.
This cost is 3 for arbitrary valid accumulators and thresholds.

It is a stipulated eager/unit-cost semantics, not a measurement of compiled
Lean short-circuit behavior. Rational operand bit lengths, accumulator construction
and history processing are not bounded by three verifier nodes. Hardware O(1),
WCET and constant time for an actual implementation are not proved.

## Method and limits

List induction gives count and flags. Composition of clipped subtraction with
nonnegative losses reduces to subtraction of their sum; monotonicity of max
transfers the total-loss bound. The fixed AST result and cost follow by unfolding
its instrumented evaluator. There are no direct Verification imports.

There is no KZG/IPA/ROM, ZK-security, authentication, actual cryptographic folding,
replay protection or arbitrary-program halting proof. A finite input list does
not establish termination of its generator. There is no quantum state or physical
error channel. Novelty is not assessed; publication, hardware authorization and
the Third Obligation are unchanged.

## Verification

See the [public source and verification record](../../docs/quantum-series-sync.en.md).
The model source is unchanged; publication checks apply to the public tree.
Historical private checks are not reused as a public full-library checkpoint.

## Proof entry points

- [accumulator_bounds_invariant](../../Verification/QuantumIVCAccumulatorContract.lean#L62)
- [fold_fidelity_nonincreasing](../../Verification/QuantumIVCAccumulatorContract.lean#L66)
- [folding_soundness_preservation](../../Verification/QuantumIVCAccumulatorContract.lean#L74)
- [count_after_fold](../../Verification/QuantumIVCAccumulatorContract.lean#L78)
- [all_valid_iff](../../Verification/QuantumIVCAccumulatorContract.lean#L84)
- [falsity_absorption](../../Verification/QuantumIVCAccumulatorContract.lean#L90)
- [false_witness_absorption](../../Verification/QuantumIVCAccumulatorContract.lean#L96)
- [folding_falsity_absorption](../../Verification/QuantumIVCAccumulatorContract.lean#L103)
- [false_history_suffix](../../Verification/QuantumIVCAccumulatorContract.lean#L115)
- [exact_fidelity_after_fold](../../Verification/QuantumIVCAccumulatorContract.lean#L140)
- [linear_fidelity_lower_bound](../../Verification/QuantumIVCAccumulatorContract.lean#L159)
- [verify_accept_iff](../../Verification/QuantumIVCAccumulatorContract.lean#L168)
- [conditional_semantic_soundness](../../Verification/QuantumIVCAccumulatorContract.lean#L173)
- [threshold_above_one_rejected](../../Verification/QuantumIVCAccumulatorContract.lean#L181)
- [nonpositive_threshold_acceptance](../../Verification/QuantumIVCAccumulatorContract.lean#L186)
- [empty_accumulator_valid](../../Verification/QuantumIVCAccumulatorContract.lean#L193)
- [foldStep_index_independent](../../Verification/QuantumIVCAccumulatorContract.lean#L196)
- [verification_constant_time_model](../../Verification/QuantumIVCAccumulatorContract.lean#L216)
- [verification_cost_history_independent](../../Verification/QuantumIVCAccumulatorContract.lean#L219)
- [verification_suite](../../Verification/QuantumIVCAccumulatorContract.lean#L252)

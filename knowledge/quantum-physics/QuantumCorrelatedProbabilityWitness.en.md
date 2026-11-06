---
id: QuantumCorrelatedProbabilityWitness
language: en
section: quantum-physics
source: Verification/QuantumCorrelatedProbabilityWitness.lean
source_sha256: f7480eacfb38411cc7db1e554e7dfc53c5d7c193aaddc30babc2e5e802c89950
novelty: not-assessed
status: reviewed
---

# QuantumCorrelatedProbabilityWitness

[Section](README.md) · [Lean source](../../Verification/QuantumCorrelatedProbabilityWitness.lean) ·
[Scope](../../docs/quantum-v4.22.md)

Builds two PSD trace-one mixtures from GHZ and its B-bit flip, with the same system
and environment marginals. Reuses the v4.21 pre-analyzer environment-controlled flip
without changing its placement. For perfect readout, the branch traces are
(1/2, 1/2, 0, 0) and (0, 0, 1/2, 1/2). The Phi+ branch of the second input is the
zero matrix by PSD and zero trace. Consequently no scalar function of the system
marginal gives the Phi+ probability on all physical joint inputs for this fixed
interaction. This strengthens the output-matrix witness with an actual probability
shift, not a claim that all interactions or all correlations cause such a shift.

## Declarations

- `QuantumCorrelatedProbabilityWitness.probability_input_zero`
- `QuantumCorrelatedProbabilityWitness.probability_input_positive`
- `QuantumCorrelatedProbabilityWitness.probability_input_trace`
- `QuantumCorrelatedProbabilityWitness.coupling_probability_prepared`
- `QuantumCorrelatedProbabilityWitness.probability_input_branch_trace`
- `QuantumCorrelatedProbabilityWitness.probWitnessPlus_valid`
- `QuantumCorrelatedProbabilityWitness.probWitnessMinus_valid`
- `QuantumCorrelatedProbabilityWitness.probWitness_same_system_marginal`
- `QuantumCorrelatedProbabilityWitness.probWitness_same_environment_marginal`
- `QuantumCorrelatedProbabilityWitness.probWitness_marginals_and_validity`
- `QuantumCorrelatedProbabilityWitness.probability_reduced_plus`
- `QuantumCorrelatedProbabilityWitness.probability_reduced_minus`
- `QuantumCorrelatedProbabilityWitness.perfect_branch_trace`
- `QuantumCorrelatedProbabilityWitness.probWitness_branch_traces`
- `QuantumCorrelatedProbabilityWitness.probWitness_phiPlus_branch_trace_shift`
- `QuantumCorrelatedProbabilityWitness.probWitness_phiPlus_minus_zero`
- `QuantumCorrelatedProbabilityWitness.no_marginal_only_branch_probability_phiPlus`
- `QuantumCorrelatedProbabilityWitness.verification_suite`

## Limits

Finite-dimensional one-cycle semantics. No adaptive process tensors, general
assignment-map classification, hardware characterization, or novelty claim.

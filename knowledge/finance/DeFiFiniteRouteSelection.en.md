---
id: DeFiFiniteRouteSelection
language: en
section: finance
source: Verification/DeFiFiniteRouteSelection.lean
source_sha256: 5cc0f981299879f5cab9a1253804ddebc2498299675f8110e313ffae2e358925
novelty: not-assessed
status: reviewed
---

# Finite candidate selection with minimum-output execution

Every supplied route is quoted against the same starting market snapshot using the reserve-updating interpreter. The selected argmax is a member of the supplied list and dominates each candidate's output. No selection occurs exactly when the list is empty. Guarded execution succeeds exactly when it returns that route's resulting state and meets the minimum-output threshold; the reserve-product guarantee is inherited. If the best route fails the minimum, every supplied candidate fails it.

Optimality concerns only the finite candidate list. Callers must provide routes with compatible input/output asset units. Exhaustive path search, gas costs, global optimality, MEV, concurrency and a changed state between quoting and execution are outside scope. Tests cover the empty and singleton lists, membership/optimality applications, and exact success/failure thresholds.

## Evidence boundary

Lean checks theorem terms and their axiom dependencies. Concrete examples and counterexamples live in the targeted regression files; they do not certify an external implementation or physical protocol. This card makes no scientific-priority claim. Exact validation results are recorded in the batch evidence.

## Theorem links

- [selected_member](../../Verification/DeFiFiniteRouteSelection.lean#L22)
- [selected_optimal](../../Verification/DeFiFiniteRouteSelection.lean#L26)
- [no_selection_iff](../../Verification/DeFiFiniteRouteSelection.lean#L31)
- [guarded_execution_iff](../../Verification/DeFiFiniteRouteSelection.lean#L38)
- [guarded_product](../../Verification/DeFiFiniteRouteSelection.lean#L45)
- [best_below_minimum](../../Verification/DeFiFiniteRouteSelection.lean#L52)
- [verification_suite](../../Verification/DeFiFiniteRouteSelection.lean#L67)

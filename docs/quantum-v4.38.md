# Quantum v4.38 — Chronological scheduled noisy repeaters

Local candidate on `acb520f3ad5e4a101b9f985a98ce450b642f0954` (v4.37),
branch `quantum-scheduled-noisy-v438`. The base is a verified local candidate;
the separately published main baseline remains `a42c09d7` (v4.21–v4.36).
This candidate is not a published release.

[Source](../Verification/QuantumScheduledNoisyRepeater.lean) ·
[Knowledge card](../knowledge/quantum-physics/QuantumScheduledNoisyRepeater.en.md) ·
[Inventory](quantum-v4.38-inventory.json)

## Operators and chronology

noisyGeneralTree extends the v4.37 tree to arbitrary PairDensity matrices. Its
scalar degree is 2^m. Each spatial level first applies the actual ideal pairSwap
to two independent child resources, then a depth-m noisy BBPSSW tree. The level's
scalar degree is B(m)=2^(m+1). The same fixed physical Visibility parameter gamma
post-depolarizes the retained pair at every internal BBPSSW node; swapping itself
remains ideal. Zero purification depth applies no depolarization.

The chronological list is evaluated with List.foldl. The accumulator explicitly
stores matrix, weight and bounded visibility. scheduledStepAcc computes the matrix
through the actual operators and independently updates the scalar fields. The
proved ScheduledState.Valid invariant binds them: D=p*isotropic(w), 0<p<=1.
No visibility is extracted from an arbitrary unnormalized matrix by division.

For each successive depth m, the updates are

- w_next=(4*noisyOrbit gamma (swapFidelity w) m-1)/3;
- p_next=p^(2^(m+1))*noisyTreeProbability gamma (swapFidelity w) m.

The append and snoc theorems make the left-to-right ordering explicit. The
isotropic matrix uses scheduledVisibility (a Visibility); its real projection
is scheduledVisibilityValue. These distinct types replace the ambiguous draft
signature. The product uses (sched.map B).prod, retaining repeated list entries.

## Proven guarantees

The final matrix has exact weight p, is PSD, and normalizes to an isotropic density
of trace one. A length-k schedule spans 2^k segments. It consumes the product of
2^(m+1) over all list entries. scheduledFold_matrix_smul proves that this product
is also the scalar degree of the actual matrix composition on arbitrary inputs.
Constant schedules have raw count 2^((m+1)*k).

Empty schedules return the input pair with weight one. All-zero schedules perform
pure ideal swapping: visibility w0^(2^k), weight one and 2^k raw pairs. At gamma=1,
a repeated depth m gives exactly nestedRepeaterMatrix m w0 k from v4.33.

LocalQualityGain quantifies over decompositions sched=pref ++ m::suffix. It asks
only that each actual step not reduce its current visibility. Under this explicit
hypothesis, every prefix and the complete schedule retain initial visibility.
No unconditional quality retention or automatic depth selection is asserted.

## Exact regressions

At gamma=19/20, w0=4/5, schedules with the same raw count can differ:

| Schedule | Final visibility | Full success weight |
| --- | --- | --- |
| 0 then 1 | 921728/2280805 | 456161/781250 |
| 1 then 0 | 8340544/19404025 | 776161/1562500 |

In the ideal case only, the schedule 4 then 2 restores visibility above 4/5 with
256 raw pairs across four segments, versus 1024 for 4 then 4. The reversed schedule
2 then 4 stays below 4/5. These inequalities are checked with exact Lean arithmetic;
no claim transfers this witness to gamma<1 or claims resource optimality.

## Verification boundaries

The gamma/scoped plan covers the quantum direction, affected external consumers,
registry integration and explicit live regressions. Direct strict module checking,
transitive axiom audit, a pinned separate compiled-declaration auditor and a
12 GiB / 4 CPU / swap=0 container run are recorded in the external evidence package.
Only propext, Classical.choice and Quot.sound are allowed. The incremental cache
is retained. No fresh beta checkpoint or new full verify-all is claimed.

Depths vary, but noise quality does not. Independent resource copies are not
unknown-state cloning; the diagonal resource composition is not a linear CP map.
Expected yield, retries, gate-internal noise, noisy swapping, asymptotic rate and
an adaptive controller are outside this module's scope.

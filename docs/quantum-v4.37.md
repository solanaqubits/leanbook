# Quantum v4.37 — Noisy BBPSSW resource trees

Local candidate on public base `a42c09d766bb6e2f32d4c1843b9de8a71a52df6c`,
branch `quantum-noisy-tree-v437`. This is not a new published release.

[Source](../Verification/QuantumNoisyBBPSSWTree.lean) ·
[Knowledge card](../knowledge/quantum-physics/QuantumNoisyBBPSSWTree.en.md) ·
[Inventory](quantum-v4.37-inventory.json)

## Operator and resource semantics

The same fixed Visibility quality is applied by noisyPurified at every internal
node of the full binary tree. Each node consumes two independently prepared
subtrees. For `F_n=noisyOrbit gamma F0 n`, the exact unnormalized state is D_n=p_n W(F_n),
where p_0=1 and p_(n+1)=p_n^2 P(F_n). The product over j<n with exponent
2^(n-1-j) represents p_n, not p_(n+1). The leaf count is 2^n.

Positivity of p_n is algebraic for real gamma,F0. The probability bound p_n<=1
and PSD density claims require physical input fidelity. The operator parameter
is Visibility. Trace equals p_n, and inverse-weight normalization returns W(F_n)
with PSD and unit trace on the physical domain. No early normalization occurs.

The actual pairSwap instrument feeds the noisy tree. Ideal corrected swapping
of two equal isotropic pairs yields a unit-trace Werner pair of fidelity
(1+3w^2)/4. A depth-n tree of such outputs consumes 2^(n+1) elementary pairs
across two segments. This is one swapping stage with temporal purification depth,
not a spatial hierarchy with noisy swapping nodes.

## Exact recovery criterion

For 0<w<1 and criticalGamma<gamma<1, finite strict recovery above
F_elem=(1+3w)/4 is possible if and only if

- lowerWindowBound(gamma)<swapFidelity(w), and
- elemFidelity(w)<upperWindowCeiling(gamma).

The proof separates necessity from sufficiency. Closed decreasing-orbit bounds
include the stationary lower and upper endpoints; the open working window
prevents overshoot. Convergence to the ceiling then yields a finite witness.
No minimal recovery depth or quantitative rate is claimed.

## Regression obligations

- gamma=1 reduces to the ideal matrix, orbit and probability.
- gamma=0 normalizes to W(1/4) at every positive depth.
- F0=1/4 gives p_n=(1/2)^(2^n-1), including p_2=1/8 and p_3=1/128.
- gamma=19/20,F0=3/4 gives p_1=13/18 and p_2=27857/72900.
- gamma=19/20,w=4/5 has a finite successful recovery depth.
- gamma=19/20,w=9/10 remains strictly below 37/40 at every depth.
- The lower fixed point and equality of the target with the upper ceiling are
  not sufficient for strict recovery; one-round recovery is not inferred from
  the existential witness.

## Verification scope

The local gamma/scoped plan includes the full quantum direction, affected external
consumers and registry integration, with an explicit live regression selection.
The new module receives strict CLI verification and transitive axiom auditing;
a pinned independent auditor checks compiled project declarations. Container
checks use 12 GiB, 4 CPU and zero swap. Results and exact commands are retained
in the external evidence package. No new full-library beta checkpoint is claimed.

Only propext, Classical.choice and Quot.sound are permitted. No proof limits,
verification rules or toolchain dependencies are relaxed. Counts refer to code,
not independent scientific results. Variable noise, expected yield, retries,
unknown-state cloning and a spatially nested noisy repeater remain outside scope.

# Quantum v4.30: BBPSSW convergence and complete binary resource trees

Local development over `3bb16017eab7b6b2550c088b629630588fa7b314`.
The published Leanbook 1.0.0 tag and public main are unchanged.

## Orbit dynamics

The existing v4.29 operator step supplies the rational recurrence R(F) and its
positive success probability P(F). Two exact algebraic barriers are proved:

- R(F)-1/4 = (4F-1)(8F+1)/(36 P(F)).
- 1-R(F) = 2(1-F)(F+2)/(9 P(F)).

Together with the previously proved sign of R(F)-F, these give invariant
intervals [0,1/4), (1/4,1/2), and (1/2,1). Orbits strictly increase in the first
and third intervals and strictly decrease in the second. Physical inputs stay
in [0,1]. The endpoints 1/4,1/2,1 remain fixed by the general fixed-orbit theorem.
No global monotonicity of the rational function on [0,1] is assumed.

Continuity is proved on all real inputs using the strictly positive denominator.
A convergent orbit has a fixed-point limit: the shifted sequence converges to
the same limit, and continuity identifies that limit with R(L). Order completeness
then yields actual Filter.Tendsto theorems:

- 1/2 < F <= 1: fidelityOrbit F tends to 1.
- 0 <= F < 1/2: fidelityOrbit F tends to 1/4.

The bounds on the supremum or infimum exclude the unwanted fixed points.
These are topological conclusions, not numerical iteration evidence or a
convergence-rate claim. R(1/10)=5/26 is an exact regression.

## Operator tree and probability

Define D_0=W(F) and D_(n+1)=purified(D_n tensor D_n). Each node consumes two
independently prepared subtrees, so a depth-n tree uses 2^n initial resources.
Bilinearity of the tensor product and linearity of the accepted, twirled map give

D_n = p_n W(R^n(F)),
p_0=1, p_(n+1)=p_n^2 P(R^n(F)),
p_n = product_(k=0..n-1) P(R^k(F))^(2^(n-1-k)).

The matrix identity is proved from the v4.29 circuit theorem purified_werner.
The weight is positive for every finite depth and every real F. For physical
F in [0,1], it is at most one and the tree matrix is PSD. Its trace is p_n.
Dividing by p_n yields exactly W(R^n(F)), with trace one and physical PSD.

This weight is the probability that all internal nodes succeed, with no recycling
or retries. It is not product_k P(F_k), an expected resource yield, or a supply
rate. At F=1/4 and depth 2, the tree weight is 1/8; the simple level product is
1/4. The regression explicitly distinguishes these quantities.

## Scope and validation

Ideal operations, identical independent Werner resources and the finite Clifford
twirl are inherited from v4.29. No cloning channel, arbitrary correlated-input
recursion, detector losses, noisy fixed point, asymptotic resource yield or
quantitative convergence rate is asserted.

Validation is scoped/gamma: strict new-module compilation and imported axiom
closure, affected registry build, independent compiled-project audit, and targeted
live tests. See [verification evidence](quantum-v4.30-verification.json).
Incremental builds and targeted tests are not a clean build or full verify-all.
The last historical full checkpoint remains v4.21 with its recorded run history.

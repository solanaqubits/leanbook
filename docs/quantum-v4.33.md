# Quantum v4.33: nested ideal repeaters

Local candidate based on `4a51f89ab8a1221041f4dabfa2e6d643b2accaa2` (v4.32).
This is a gamma/scoped addition. Public Leanbook 1.0.0 and main are unchanged.

## One-round limit and the local comparison

`QuantumNestedRepeater` proves the exact factorizations of w-g(w) and g(w)-w²,
where g is the existing `nodeVisibilityValue`. Its only fixed points on [0,1]
are zero and one. Continuity, the antitone bounded orbit, and the fixed-point
identity of its limit give genuine `Filter.Tendsto` theorems: visibility tends
to zero for initial Visibility below one, and target fidelity tends to 1/4.

For 0<w<1 with w²>1/3, w²<g(w)<w is a local benefit over swapping alone.
It does not propagate from the initial threshold hypothesis alone:

- w0=3/5 has w0²=9/25>1/3 and g(w0)=129/353>9/25.
- g(g(w0))=875821377/7902162881<81/625=w0⁴.

At the second node the current squared visibility is below the BBPSSW threshold.
The counterexample is a kernel-checked theorem, not a floating-point comparison.

## Nested operator and resource law

`purifiedTree m M` repeatedly applies the existing linear CP instrument `purified`
to two independent copies of its previous unnormalized output. It is homogeneous
of degree 2^m in M and equals the v4.30 `treeMatrix F m` on `werner F`.
`nestedRepeaterStep m D` applies this tree to `pairSwap D D`.

For fixed depth m per spatial level, put B=2^(m+1) and
Q_m(w)=treeProbability(swapFidelity(w),m). The proved recursions are

    w_(k+1) = (4*R^m((1+3*w_k^2)/4)-1)/3
    p_0 = 1
    p_(k+1) = p_k^B * Q_m(w_k)
    D_k = (p_k : Complex) • isotropic(w_k).

For every m and finite k, p_k is positive and at most one, D_k is PSD, and its
trace equals p_k. Conditioning by p_k gives a PSD unit-trace isotropic state;
its target overlap is elemFidelity(w_k). No normalization is inserted during
construction of the recursive operator output.

Spatial span remains 2^k segments. Raw resource count is B^k=2^((m+1)*k),
equivalently 2^(m*k) independent raw pairs per segment.
At m=0 the model reduces to pure ideal swapping, visibility w0^(2^k), weight one.
At m=1 the matrices, visibility and probabilities coincide with v4.32.
A regression at m=2, w0=0, k=2 gives p2=2^(-27), not a product of just two
local probabilities. At m=4 a single spatial level consumes 32 raw pairs;
two levels consume 1024 raw pairs across four segments.

## Conditional quality at every finite scale

The module proves strict input monotonicity of BBPSSW recurrence on [1/4,1]
and of the nested visibility map on [0,1]. Therefore a strict gain at the first
spatial level implies strict growth of the entire spatial-level orbit.
Every positive level exceeds the initial visibility and fidelity; every finite
level remains strictly below one. The concrete choice m=4 and w0=4/5 has a
kernel-checked first-step gain and hence exceeds fidelity 17/20 at every
positive level.

This is not a claim that nested orbits converge to one. Such a limit would
require a separate fixed-point analysis of the composed swapping/purification
map. It also does not assert nonzero asymptotic success probability, expected
yield, generation rate, retries, recycling, scheduling, memory lifetimes,
gate noise, detector losses, or arbitrary correlated resources. Repeated-copy
parametrizations represent independent preparation, not cloning channels.

## Verification scope

The addition has 45 named theorems and 57 named exports (11 definitions and one
suite structure besides theorems). These are code metrics, not counts of
independent scientific results. See the [inventory](quantum-v4.33-inventory.json)
and [verification report](quantum-v4.33-verification.json).

Validation consists of strict module elaboration and transitive axiom audit,
affected registry/integration build, independent audit of compiled project
declarations, targeted container regressions, metadata and knowledge checks.
It is not a fresh full verify-all, full test discovery, or clean build. The last
historical full checkpoint remains v4.21 with its original qualifications.
No scientific-priority claim is made. No public release or push is performed.

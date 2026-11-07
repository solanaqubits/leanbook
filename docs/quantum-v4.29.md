# Quantum v4.29: ideal BBPSSW recurrence and finite local Clifford twirling

Local development over `96b8f303ca3e5e0fd047b4ef98f8828daf43062d`.
The published Leanbook 1.0.0 tag and public main are unchanged.

## Operator contract

The register order is (A1,B1,A2,B2). The bilateral CNOT is a sparse permutation
(a,b,c,d) -> (a,b,c+a,d+b) over Fin 2. Its unitarity is proved. Four rectangular
measurement operators retain the first pair and measure the second pair.
Equal target bits are accepted; unequal target bits are rejected. The two
unnormalized instrument maps are CP and their traces sum to the input trace.
No input PSD assumption is needed for this algebraic trace identity.

The Werner input is specified by Bell weights F,(1-F)/3,(1-F)/3,(1-F)/3.
For F in [0,1] it is a density matrix. Two independent preparations supply the
tensor product; there is no universal quantum cloning channel.
The accepted matrix is derived from the circuit before defining conditioning:
its Bell weights are F^2+g^2, 2Fg, 2g^2, 2g^2, where g=(1-F)/3.

## Finite twirl

QuantumCliffordTwirl explicitly averages four local Pauli actions followed by
three powers (0,1,2) of a local cycle, using U tensor conjugate(U). This gives a
finite ensemble of twelve sequential local Clifford operations. The cycle is a
unitary that normalizes the Pauli matrices, fixes the Phi+ projector and cycles
the other three Bell projectors. The Pauli average removes Bell coherences but
does not equalize the diagonal weights. The subsequent cycle average does.

The full formula is proved for every complex 4x4 matrix, not just density inputs:
T(M) = f Pi(Phi+) + (trace(M)-f)/3 * (I-Pi(Phi+)), with f=targetOverlap(M).
CP, complex linearity, trace preservation and target overlap preservation are
proved separately. The formula is a theorem of the finite matrix ensemble,
not the definition of the channel.

## Recurrence and threshold

P(F)=F^2+2F(1-F)/3+5(1-F)^2/9 is strictly positive (in fact for every real F).
The twirled accepted matrix is exactly P(F) times W(R(F)), where
R(F)=(F^2+(1-F)^2/9)/P(F). Conditional normalization therefore gives W(R(F)).
For F in [0,1], R(F) is in [0,1], with a PSD trace-one conditional matrix.
The recurrence difference factors as (1-F)(4F-1)(2F-1)/(9P(F)).
Its fixed points are exactly 1/4,1/2,1. Strict increase holds below 1/4 and
between 1/2 and 1; strict decrease holds between 1/4 and 1/2.
Increasing a low target overlap below 1/4 is not a claim of useful distillation.

## Scope

This is one ideal BBPSSW round with equal, independent Werner resources.
No detector losses, gate noise, arbitrary correlated resource theorem, resource
optimization, asymptotic yield, or convergence of repeated rounds is asserted.
The CP claims apply to unnormalized maps on the full joint input; conditioning
and the parametrization by two identical copies are separate nonlinear steps.

Verification is scoped/gamma, recorded in quantum-v4.29-verification.json.
Incremental builds are distinguished from clean rebuilds, and targeted tests
from full-library discovery. Development and failed fixture logs are retained.

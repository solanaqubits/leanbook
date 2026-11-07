# Quantum v4.31: heterogeneous BBPSSW and swap-then-purify

Local development over `b809738911b60cd4228f64fc2067c6cf437c86a7`.
The published Leanbook 1.0.0 tag and public main are unchanged.

## Unequal independent resources

For g1=(1-x)/3 and g2=(1-y)/3, the existing v4.29 bilateral circuit gives
accepted Bell weights (xy+g1*g2, x*g2+g1*y, 2*g1*g2, 2*g1*g2).
The matrix equality is derived entrywise in four row lemmas. Target overlap
and trace give N2=xy+(1-x)(1-y)/9 and P2=(8xy-2x-2y+5)/9.

The constructive Clifford twirl then proves, for every real x,y,

purified(W(x) tensor W(y)) = N2 Pi(Phi+) + (P2-N2)/3 (I-Pi(Phi+)).

If P2 is nonzero this equals P2 W(R2), where R2=N2/P2. Physical x,y in [0,1]
give 1/3 <= P2 <= 1, 0 <= R2 <= 1 and a PSD trace-one conditional matrix.
The nonzero premise cannot be dropped: at (1,-1/2), P2=0 but N2=-1/2,
and the purified matrix is nonzero. This input is not a physical density matrix.
Symmetry and the diagonal reduction P2(F,F)=P(F), R2(F,F)=R(F) are proved.
The CP and trace-balance properties of the underlying instrument are inherited
from v4.29; the product parametrization and conditional normalization are nonlinear.

## Improvement depends on both inputs

The exact numerator of R2(x,y)-x is
(-8x^2+12x-1)y+2x^2-6x+1, divided by 9P2.
For 1/4<x<1 and 0<=y<=1, improvement occurs exactly when

y > thresholdFor(x) = (6x-2x^2-1)/(-8x^2+12x-1).

The denominator is positive on [1/4,1]. Its square completion is
7/2 - 2(2x-3/2)^2, not 7 - 2(2x-3/2)^2.
Simultaneous improvement above max(x,y) requires both threshold inequalities.
Having both input fidelities above 1/2 is not sufficient: R2(3/4,3/5)=83/118<3/4.
The missing term in the previously proposed numerator was (y-x)(2x+1), without
an additional factor 9. In contrast, R2(1/2,3/4)=7/11>1/2; thresholdFor(3/4)=19/28.

## Operator bridge from swapping

swapOutput is the sum of the four actual perfect-readout wernerRound branches,
with identity pre/post depolarization parameters and independent spectator memory.
The v4.27 operator theorem proves swapOutput=W(Fswap), Fswap=(1+3w^2)/4.
swapThenPurify applies purified to two independently generated swapped outputs,
allowing different memory dimensions. Its unnormalized matrix is P(Fswap) W(R(Fswap));
conditional normalization gives W(R(Fswap)). This is not an output defined by the scalar law.

For 0<w<1, one purification step always remains below Felem=(1+3w)/4:

R(Fswap)-Felem = -w(1-w)(3+w+w^2-3w^3)/(4(1+w^4)) < 0.

When w^2>1/3 it nevertheless strictly improves Fswap. Using the v4.30 Tendsto theorem,
every sufficiently large finite purification depth exceeds Felem; existence is a
corollary. Each such depth consumes independent swapped resources, not repeated
use of one pair or a cloning channel. No expected yield or optimal depth is claimed.

At w=4/5, Fswap=73/100 < R(Fswap)=2705/3524 < Felem=17/20.
The proposed depth-2 witness was incorrect: the second iterate is 3695777/4583300,
and the third is also below 17/20. Exact Lean regressions prove that depth 4 is
the first depth exceeding 17/20 in this example (16 swapped pairs, 32 elementary pairs).

## Validation scope

See [verification evidence](quantum-v4.31-verification.json). The scoped/gamma gate
covers strict elaboration and imported axiom dependencies, affected registry build,
independent compiled audit, and targeted live regressions. It does not replace the
historical full v4.21 checkpoint or constitute a clean rebuild.
No detector losses, noisy BBPSSW gates, correlated resource formulas, general
policy optimization, finite-rate yield or quantitative asymptotic rate are claimed.

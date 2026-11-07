# Quantum v4.32: finite ideal repeater chain

Local development over `6493e45b7bb78ba41ac732b0f166988c58dd7b2b`.
The published Leanbook 1.0.0 tag and public main are unchanged.

## Concrete scope

The repeater is a homogeneous chain of 2^k elementary segments, with ideal
operations and independent initial Werner resources of visibility w0 in [0,1].
Each level performs one swapping step and exactly one BBPSSW purification round.
The two purification inputs are identically distributed, so this is the diagonal
case of the heterogeneous protocol, not a claim about arbitrary unequal network links.

The existing ideal acceptedMap acts on M tensor N to define pairSwap. Four
independent child resources A,B,C,D feed a node:

repeaterNode(A,B,C,D) = purified(pairSwap(A,B) tensor pairSwap(C,D)).

The recursive all-success matrix uses four independently prepared copies of the
previous level's resource. No conditional division is performed inside this
construction. Tensor products denote independent resources, not a cloning channel.
The node expression is multilinear in four inputs; using one common parameter for
the copies does not make it a linear CP map of a single pair.

## Operator refinement and probability

The previous circuit theorems give exact matrix identities for pairSwap and the
purification node. Induction proves, at every finite depth,

D_k = p_k isotropic(w_k),
w_(k+1) = 2 w_k^2 (1+2w_k^2) / (3(1+w_k^4)),
p_0 = 1, p_(k+1) = p_k^4 (1+w_k^4)/2.

The visibility remains in [0,1]. Each level's conditional acceptance probability
(1+w_k^4)/2 is in [1/2,1]. The total all-success weight p_k is strictly positive,
at most one, and equals the complex trace of D_k. The exact closed form uses
product_(j<k) ((1+w_j^4)/2)^(4^(k-1-j)).

The matrix D_k is PSD. Dividing by its positive trace gives exactly isotropic(w_k),
with PSD, trace one and target fidelity (1+3w_k)/4. These identities are proved
from the recursively composed operators; they are not definitions of D_k.

## Spatial length and consumed resources

segmentCount doubles per level and equals 2^k. rawPairCount quadruples and equals
4^k = segmentCount(k) * 2^k. Thus the chain uses 2^k initial raw copies per segment
under this complete, independent, no-retry construction. Segment count alone is
not the consumed resource count. A depth-two example has four spatial segments
and sixteen raw pairs. With elementary visibility zero, its all-success weight
is (1/2)^4*(1/2)=1/32, not the binary-purification value 1/8 or the level product 1/4.

The probability requires all child nodes to succeed. It is not an expected yield,
a supply rate or a model that recycles successful children after another child fails.
No physical length unit or propagation-time law is introduced; distance is counted
in elementary segments, optionally interpreted as 2^k times an externally supplied l0.

## Quality boundary

The full node fidelity is R((1+3w^2)/4). The v4.31 inequality shows that it is
strictly below the previous level's (1+3w)/4 whenever 0<w<1. Consequently the
visibility sequence is nonincreasing, and strictly decreasing for interior inputs.
For w=4/5, the next visibility is 608/881<4/5 and the local success probability
is 881/1250. The node visibility has fixed endpoints 0 and 1.

One BBPSSW round per swapping level therefore does not establish a repeater with
quality bounded away from full mixing over arbitrary distances. Additional
purification rounds, resource policies or error-corrected architectures would
require separate work. No limit theorem or quantitative convergence rate for
this new recurrence is claimed here.

## Validation

See [verification evidence](quantum-v4.32-verification.json): scoped/gamma strict
verification, imported axiom closure, affected registry build, independent
compiled-project audit and targeted tests. This is not a new full verify-all,
full test discovery or clean build. The historical full checkpoint remains v4.21.
No memory decoherence, noisy gates, losses, adaptive scheduling, correlated-input
recurrence, hardware performance or deterministic end-to-end channel is asserted.

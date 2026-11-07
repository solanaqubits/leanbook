# Quantum v4.34: post-depolarized BBPSSW

Local gamma/scoped candidate based on `ad83f5a23cade7b6d58ae7f2447d21a06e1c9b69`
(v4.33). Public Leanbook 1.0.0 and main remain unchanged; no push or release.

## Exact operator model

`noisyPurified gamma M = (depolarizing gamma).map (purified M)` composes the
existing ideal BBPSSW instrument and finite Clifford twirl with a trace-preserving
depolarizing channel on the entire retained pair. Gamma has type Visibility.
This is post-processing noise, not a general model of bilateral CNOT errors,
input noise, measurement errors or noisy networking hardware.

For every joint input matrix, the composite map is CP, complex linear and
preserves the trace of the accepted purified output. It preserves PSD and,
together with the unchanged rejected branch, has full trace balance.
On two independent Werner inputs the proved matrix identity is

    noisyPurified gamma (W(F) tensor W(F)) = P(F) • W(R_gamma(F))
    R_gamma(F) = (1-gamma)/4 + gamma*R(F).

The matrix identity and trace P(F) hold for all real F. Physical conditional
density claims cover F in [0,1], including below 1/4. Dividing by P(F)>0 gives
a PSD unit-trace Werner state. Pre-depolarizing both inputs instead would change
the argument to F_gamma and the success probability to P(F_gamma); that is not
the implemented model.

## Fixed points and working window

The exact factorization is

    R_gamma(F)-F = (4F-1)*Delta_gamma(F)/(36*P(F))
    Delta_gamma(F) = -8F^2+4*(2*gamma+1)*F-(5-gamma)
    d(gamma) = 4*gamma^2+6*gamma-9
    Delta_gamma(F) = (d(gamma)-(4F-(2*gamma+1))^2)/2.

Thus the numerator is cubic. The quadratic factor remains after separating the
universal fixed point F=1/4. Set gamma_c=3*(sqrt(5)-1)/4.

- For 0<=gamma<gamma_c, the discriminant factor is negative. F=1/4 is the only
  real fixed point; every F>1/4 strictly decreases in one step.
- At gamma=gamma_c, the quadratic is -8*(F-(2*gamma_c+1)/4)^2. Fixed points are
  1/4 and the double root (2*gamma_c+1)/4; there is no strict gain for F>=1/4.
- For gamma_c<gamma<1, define F_minus/plus=(2*gamma+1 minus/plus sqrt(d(gamma)))/4.
  The module proves 1/2<F_minus<F_plus<1. For F>1/4, strict improvement occurs
  exactly when F_minus<F<F_plus. Fixed points are exactly 1/4 and the two roots.

The upper stationary root is strictly below R_gamma(1), which is itself below
one. It is not a universal upper bound on transient outputs. No convergence of
iterates to this root or to 1/4 is asserted in this version.

## Exact regressions

- Gamma=1 recovers R(F), with roots 1/2 and one.
- Gamma=0 gives conditional fidelity 1/4 for every real F.
- Gamma=9/10 is strictly subcritical and has no working window.
- Gamma=19/20 is strictly supercritical; R_gamma(3/4)=99/130>3/4.
- R_(19/20)(1)=77/80; the stationary ceiling is (29+sqrt(31))/40<77/80.
- The ceiling is actually a fixed point; 3/4 lies strictly inside the window.
- Operator regressions include PSD, linearity, probability preservation, complete
  post-depolarization, and normalization of the physical input F=0.

## Validation and boundaries

One module contains 42 named theorems and 50 exports (seven definitions and one
suite structure besides theorems). These are code metrics, not counts of
independent scientific results. The registry field is `noisy_bbpssw`.
See the [inventory](quantum-v4.34-inventory.json) and
[verification report](quantum-v4.34-verification.json).

Checks are strict elaboration and transitive axiom audit, affected integration
build, independent compiled-project axiom audit, targeted container regressions,
metadata and knowledge checks. This is not a full verify-all, full test discovery
or clean build. The last historical full checkpoint remains v4.21 with its
original qualifications. No scientific-priority claim is made.

The model uses two independently prepared identical resources. Neither that
parameterization nor conditional normalization is claimed to be a linear CP
single-input cloning map. No noisy-repeater limit, resource rate, expected yield,
retry model, gate threshold beyond this specified channel, or iteration limit
is included.

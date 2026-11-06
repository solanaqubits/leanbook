# Quantum v4.27 — Werner cascade reduction and fixed points

Local scoped/gamma addition on `d54e87cf10c7f50f2caeb66dcd6dd67c0acfccfc`
(v4.26), branch `quantum-werner-v427`. Published Leanbook `v1.0.0` is unchanged.
No toolchain, dependency or verifier-policy change.

[Exact inventory](quantum-v4.27-inventory.json) ·
[Verification record](quantum-v4.27-verification.json)

## Operator refinement

`QuantumWernerCascade.preStages` applies a specified channel before the entire
Bell analyzer, with spectator environment. `preRound_map` proves exact equality
with the existing `noisyOutcome` on the system marginal for every matrix and
outcome. This fixes the channel insertion cut; it is not an arbitrary model of
noise within a physical CNOT gate.

`wernerRound` chooses central BC isotropic depolarization, perfect readout and
full-pair AD isotropic post depolarization. This is the pair-noise model; existing
D-only refinements keep their earlier hypotheses and are not generalized here.
`wernerCascade` uses a fixed fresh Werner pair and independent fresh second memory,
with second-round parameters identical for every delivered first message.

`cascade_visibility_matrix` evaluates the actual `QuantumCascadedSwapping` branches
and proves equality of the complete accepted output matrix with an isotropic state
of visibility

`c₂ * b₂ * c₁ * b₁ * w₁ * w₂ * w_fresh`.

The inputs are two Werner pairs independent of the first memory. The memories may
have different arbitrary finite dimensions. The first memory is discarded. Kraus
preparation supplies both the fresh pair and the fresh second memory. Because the
continuation is identical for every first message, complex linearity permits
aggregation before the second round. No per-message equality is assumed.

The accepted aggregate has trace one and is PSD. Its target overlap is therefore
already its normalized fidelity. `cascade_fidelity_transition` identifies this
matrix quantity with the scalar transition from the first-round visibility.
`cascade_fidelity_nonincrease` then imports the proved scalar inequality.
No desired output matrix or scalar product is postulated as a premise.

## Scalar consequences

`QuantumCascadeReduction` retains the explicit real parameters and [0,1] bounds.
It proves bounds on alpha, preservation of [0,1], nonincrease for nonnegative
visibility, strict decrease for w>0 and alpha<1, and the full equality condition:

`T(w) = w` iff `w = 0` or `alpha = 1`.

The same condition characterizes equality of fidelity. There is no distillation
threshold in this model. At alpha<1 the only fixed point is w=0 (F=1/4); at alpha=1
all inputs are fixed.

Constant-parameter iteration is `alpha^n * w`. A finite schedule with varying
parameters gives their finite product and is nonincreasing. Actual convergence
is proved separately with `Tendsto`: for constant alpha<1, visibility tends to zero
and fidelity tends to 1/4. For nonnegative inputs the approach is from above;
alpha=0 can reach 1/4 after a single step. A varying schedule has no general
convergence guarantee without further assumptions. The code uses Function iteration,
not the proposed Nat.iterate form, and closes the correct namespace.

## Checks and boundaries

The two modules contain 28 named theorems and 42 named declarations in the export
inventory, including definitions, structures and suites. These counts are code
metrics, not independent scientific results.

New regressions check alpha=0 and alpha=1, strict loss at positive visibility,
finite iteration, the separately stated limit and its direction. Operator fixtures
use memories of dimensions 2 and 3: three input pair visibilities of 1/2 give
F=11/32 with ideal gates; two additional factors 1/2 in round two give F=35/128.
They also check the output matrix itself and trace one. Prior cascade, feedback,
zero-branch, post-noise and environment fixtures remain in the targeted set.

Validation is scoped/gamma: strict elaboration of both new modules, imported axiom
closure, incremental root build, targeted container regressions and independent
compiled-project audit. Exact results and attempt history are in the verification
record. No new full verify-all, full test discovery, clean build or remote CI claim.

This is not a universal monotonicity law for CPTP channels. Arbitrary readout,
postselection, message-dependent resources, correlated fresh inputs and general
noise need not obey this visibility product. No distillation circuit, retained
memory process tensor or hardware calibration is supplied. The finite-iteration
and limit theorems concern the scalar recurrence; the new operator instrument
refinement covers exactly the existing two-round cascade.

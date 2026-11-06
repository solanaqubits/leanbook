# Quantum v4.28: adaptive Werner cascade with detector loss

Local additive candidate over `3cdac4021bf5c9b574116c19dec2461125b9e31c`.
The published Leanbook 1.0.0 tag is unchanged.

The first result proves each individual corrected Bell sandwich, then includes
central BC depolarization, full-pair AD post depolarization, and faithful delivery
with detector efficiencies in [0,1]. It does not infer individual branches from
an aggregated equality. Each initial Werner pair is independent of the other
and of the first memory.

The actual v4.26 Cascade chooses second-round noise, a fresh Werner pair and
fresh independent memory by the delivered first message. Each successful history
has weight eta1(r)*eta2(r,t)/16. Summing gives q(r) and total success P. The exact
matrix sum, trace P, zero matrix at P=0 and normalized affine Werner matrix at
P>0 are proved. Conditional visibility is bounded in [0,1]. Selected branches
also have an explicit conditional matrix formula. The target-overlap lemma
connects these matrices to the scalar fidelity comparison.

A positively weighted branch above the weighted mean beats the aggregate fidelity
but cannot exceed the first-round fidelity. This is not global policy optimization
or entanglement distillation. Arbitrary label confusion is outside the Werner
specialization; the general underlying instrument retains that capability.

The affine `wernerMatrix` accepts real scalars algebraically; physical operator
channels use bounded `Visibility`. The conditional bound is separately proved.
First memory is discarded; no persistent multi-round environmental correlations
or process tensor model are claimed.

Validation scope is gamma: strict module/import closure, incremental registry
build and targeted regressions. See the verification JSON for actual results;
these do not constitute a new full-library test discovery or clean build.

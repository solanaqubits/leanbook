---
id: CryptoHiddenScalarTapeAverageContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarTapeAverageContract.lean
novelty: not-assessed
status: reviewed
---

# Weighted adversary tapes and dependent schedule laws

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarTapeAverageContract.lean)

## Exact result

`TapeLaw` supplies rational nonnegative weights on a finite tape type, summing to
one. `TapeExperiment` uses a common initial memory and a single transition function
whose first argument is the tape. `model w` fixes that tape for the entire collector,
including restores. All tapes use the same public `claim`, field, group and IPA depth.
The plan and threshold profile may vary with the tape. Each plan retains epsilon219's
finite independent microseeds, common shape and budgets per depth, and decoders
indexed by exact snapshots. Seed spaces may therefore have different cardinalities.

`qualifies` means that the actual epsilon220 single-path acceptance rate on this tape
is at least its chosen root threshold. `guardedBound` is epsilon221's computed bound
when this premise holds and zero otherwise. It is always in [0,1]. In particular,
an aborted or rejected tape cannot inherit a positive unguarded threshold bound.

`jointMass` assigns `(w,v)` mass `W.weight w / card (Seed w)`. The fiber sum is
exactly the tape weight and `jointMass_total` proves total mass one. This is sequential
sampling, not uniform sampling on the disjoint union of unequal seed spaces.
The conditional uniform microseed law is exactly the law certified by `ProtocolPlan`;
its decoded schedule distribution retains multiplicities. No arbitrary conditional
law is substituted without a correspondence proof.

`jointRate_eq_average` proves exact finite event decomposition.
`averaged_acquisition_lower` states that the expectation of guarded bounds is at most
`successProbability`, the joint-law probability that the actual epsilon215 collector
returns an ok fork. The expectation is a lower bound, not an exact success probability.
`averaged_pos_iff` characterizes strict positivity by existence of a positive-weight
tape that qualifies and has strictly positive computed threshold bound.

`positive_mass_extracts` then gives a tape and a seed of positive joint mass, a real
successful `acquireCompressedFork` result, `ForkProvenance`, and `ResultValid` for the
existing `extractCompressed`: valid witness OR nontrivial generator relation.
No new collector or extractor is defined. The result is existential, not an algorithm
for locating the tape/seed with bounded cost.

## Regression evidence and limits

Exact rational regressions distinguish tape weights 2/3 and 1/3 from a uniform
union with fiber sizes 1 and 3 (the latter would give 3/4 instead of 1/3).
Repeated accepting microseed images contribute 2/9. A real depth-zero F5 model uses
one aborting and one honest tape, with outer budgets 4 and 3, eta budget 2, and seed
cardinalities 40960000 and 512000. Its honest threshold bound is
`14536674033/125000000000` and guarded expectation is one third of that value.
An explicit acquired fork is passed to the existing extractor and yields the zero
witness. Further cases cover zero tape weight, insufficient budgets, flat cutoffs
with zero bound despite a successful schedule, and a failed scalar check.

Positive global acceptance alone does not imply a positive guarded expectation.
Density margins and sufficient budgets remain sufficient ways to establish
positivity, not necessary physical conditions for actual success. Infinite tape
spaces, arbitrary replacement conditional laws, external-process refinement,
Fiat–Shamir/ROM, polynomial complexity and hardware runs are not established.
Validation is scoped; historical full beta bases are retained. Novelty is not assessed.

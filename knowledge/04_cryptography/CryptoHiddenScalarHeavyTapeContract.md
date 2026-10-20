---
id: CryptoHiddenScalarHeavyTapeContract
language: en
section: cryptography
source: Verification/CryptoHiddenScalarHeavyTapeContract.lean
novelty: not-assessed
status: reviewed
---

# Weighted heavy tapes and quota margins

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoHiddenScalarHeavyTapeContract.lean)

## Exact statements

`TapeLaw.mass` measures a finite set under epsilon222's normalized nonnegative
rational tape weights. `heavy_mass_lower` derives
`max(0,(E[a]-theta)/(1-theta)) <= mass {theta <= a}` for `theta < 1` and `a <= 1`.
The proof is a weighted finite split; it does not replace tape weights by uniform
cardinality. `qualifying_mass_lower_of_cap` allows a varying cutoff tau(w) bounded
above by theta. Its cap premise is stated for every tape, including zero-weight ones.

`variable_threshold_split` gives the separate bound
`E[a] <= E[tau] + E[1_{tau<=a}*(1-tau)]`.
For nonnegative tau, `variable_mass_lower` yields `max(0,E[a]-E[tau]) <= mass H`.
The average threshold cannot be substituted in the constant-cutoff fraction:
with equal weights, a=(1,4/5) and tau=(1/10,9/10), actual qualifying mass is 1/2
while the invalid substitution gives 4/5. `mass_one_of_acceptance_one` handles
E[a]=1 and tau<=1 separately, without division by zero: qualifying mass is one.

`expectation_lower_on_set` and `good_mass_lower` retain a good subset G of qualifying
H. If mass H>=m, mass(H\G)<=epsilon, b>=0 and the computed quota bound is at least
b on G, `averaged_lower_with_exception` gives `b*max(0,m-epsilon) <= averagedBound`.
If b>0 and epsilon<m, `good_tapes_extract` reuses the existing positive-mass extractor.

`global_acceptance_lower` and `global_success_lower` instantiate the weighted bound
with actual single-path `acceptanceRate`: a global lower bound alpha, a common root
threshold cap theta<1, and a separate quota margin b on every qualifying tape imply
`b*max(0,(alpha-theta)/(1-theta)) <= averagedBound <= successProbability`.
`global_acceptance_extracts` requires theta<alpha and b>0. Its conclusion supplies
an actual tape/seed pair of positive joint mass, successful `acquireCompressedFork`,
`ForkProvenance` and `ResultValid` for `extractCompressed` (witness OR generator relation).

## Preserved laws and limits

The same TapeExperiment transition function, common claim and initial memory are
used. Each tape retains its original finite ProtocolPlan microseed law and decoder,
with potentially different seed-space sizes and budgets. Neither tape selection nor
schedule selection is conditioned on the heavy or good subset. No new collector,
extractor, search procedure, ROM theorem or polynomial-time bound is introduced.
Global acceptance alone does not supply a positive quota margin. Zero conservative
bounds do not rule out actual successful runs. Novelty is not assessed.

## Regression scope

Kernel rational checks cover nonuniform and zero weights, the invalid average-cutoff
substitution, theta=1, exceptional mass, unequal seed fibers and repeated accepting
images. A real depth-zero F5 model tests the global bridge and executable zero-witness
extraction; abort costs remain Q=1,R=0. A positive-mass qualifying set with a flat
profile has zero lower expectation despite a concrete successful schedule.
Live tests are finite model checks, not hardware or external-process validation.

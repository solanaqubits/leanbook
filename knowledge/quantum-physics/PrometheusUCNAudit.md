---
id: PrometheusUCNAudit
language: en
section: quantum-physics
source: Verification/PrometheusUCNAudit.lean
source_sha256: 10f7bfa659d0b708cf168e0620ca74ead6b4121ef7f513bac64d3155c910bea6
novelty: not-assessed
status: reviewed
---

[Lean](../../Verification/PrometheusUCNAudit.lean)

# Conditional UCN kinetics and mass-energy accounting

Epsilon246, quantum-physics/prometheus-audits. The cross-section law, EOS
approximation and hypothetical energy yield are separate inputs. Existence of
a bound multineutron state is neither assumed as a result nor proved.

Given crossSection k v=k/v and v>0, rate_eq proves reactionRate n k v=n*k.
The model defines holdingProbability n k v t=1-exp(-reactionRate n k v*t).
At the same holding time this is identical for any two positive velocities.
Density and k are arbitrary for the algebraic identity; physical interpretation
needs positivity. For a fixed slab L>0,n>0,k>0, residence time is L/v and
slabProbability=1-exp(-n*k*L/v). slab_eq_holding equates this to holding probability
at that time; slab_strict_decrease proves strict decrease with positive velocity.
The increase on slowing is due to increased residence time. Applicability of a
1/v formation law to neutron clusters is not established.

N,Z are natural counts, both cast to Real before delta=(N-Z)/(N+Z). With Z=0,N>0,
neutron_asymmetry proves delta=1; an empty cluster is excluded. In the supplied
parabolic model at one saturation density, eosAtSaturation S delta=-16+S*delta^2.
For S>=30, neutron_energy_lower_bound gives E/A>=14>0 for pure neutrons; symmetry
gives-16. This is not a theorem excluding every bound state at every density or
finite clusters. Topological confinement and an experimental S are not derived.

qValue N m M c=(N*m-M)*c^2 in consistent units. q192_iff_mass proves exactly
qValue 12 m M c=192 iff M*c^2=12*m*c^2-192. This rearranges an energy balance;
it does not establish M, a state, a decay channel or a192MeV gamma photon.
Binding energy is not subtracted twice.

Conditionally assuming16MeV per neutron and10000neutrons, with exact
1MeV=1.602176634e-13J, gross_exact and gross_bounds give
E_gross=2.5634826144e-8J<26nJ. Given E_input>=1J, net_deficit proves a negative
net balance. The1J condition is not a universal estimate of trapping costs.
Heat, light output, biomatrix efficiency and SiPM efficiency are distinct.

Other declarations: fixed_time_invariant and verification_suite. Registry field:
QuantumPhysicsFullSuite.prometheus_ucn_audit; no direct Verification imports.
Original targeted verification reported52 declarations with approved axioms only;
23examples test values, slab ordering, v/n/N positivity, S/input-energy boundaries
and conditional masses. The two audits plus registry have3live tests and67examples.
Failures and commands are retained as historical scoped evidence, not a new full
beta or a physical reactor/sensor/QPU validation. Novelty not assessed. Hardware
admission, authorization and Third Obligation remain unchanged.

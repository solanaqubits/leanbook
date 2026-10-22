---
id: PB11EnergyBalance
language: en
section: quantum-physics
source: Verification/PB11EnergyBalance.lean
source_sha256: ad87463433482630939ea73a9f2b9d28d1a6ed77ded4edee4e418c712f4dc80a
novelty: not-assessed
status: reviewed
---

[Lean](../../Verification/PB11EnergyBalance.lean)

# Conditional p-B11 shot energy balance

Epsilon247, quantum-physics/pb11-energy. Proofs concern exact Real formulas;
reaction probability, laser acceleration and energy extraction efficiency are
external inputs.

PB11Reaction contains nonnegative rest energies in MeV and the premise
m_p+m_B=3*m_alpha+Q, with Q=87/10. For kineticOut k=k+Q,
energy_conservation equates total energies before and after reaction. This is an
algebraic consequence of the supplied mass defect, not validation of measured
masses.8.7MeV is exact in the model and a rounded physical input.
MHDExtractor stores B,v and energetic efficiency eta in[0,1]. For workOut K=eta*K
and K>=0, workOut_nonneg and mhd_bound prove nonnegative bounded output. Charge
collection efficiency alone is insufficient; B and v do not determine eta.

Shot has laser energy L in J, proton energy E and Q in MeV, a,p,eta in[0,1],
L>=0,E>0. Proton and reaction counts are Real expectations. The exact MeV-to-J
factor is1.602176634e-13. fusion_from_count links F=p*a*L*Q/E to reaction count.
Alpha energy A=p*a*L+F includes kinetic energy of reacting protons. Electrical
output W=eta*A; losses are L1=(1-a)*L, L2=(1-p)*a*L, L3=(1-eta)*A.
shot_balance proves L+F=W+L1+L2+L3; losses_nonneg proves all losses nonnegative;
electrical_le_available gives W<=L+F. Nuclear energy consumes fuel rest energy.

For frequency f>=0, wall efficiency0<w<=1, auxiliary energy a_s>=0J/shot and
standing load P_s>=0W, netPower=f*(W-L/w-a_s)-P_s.
net_nonpositive_of_no_gain proves netPower<=0 when W<=L;
baseline_net_nonpositive applies this to the selected scenario.
For L=1.5J,a=0.1,p=1e-4,E=0.675MeV,Q=8.7MeV,eta=0.6:
F=29/150000J,A=1/4800J,W=1/8000J. At1000Hz gross output is1/8W;
1kW gross needs8MHz. W/L=1/12000 or0.008333...percent. Even with ideal wall power
and zero auxiliaries, net power at8MHz is-11.999MW. This is a scenario result,
not a universal prohibition of p-B11 energy production.

Proofs use linarith, ring, norm_num, product positivity and division by positive
numbers. There are no internal Verification imports. PB11EnergyBalanceSuite is
exported through QuantumPhysicsFullSuite.pb11_energy. Original targeted verification
reported152 declarations with propext/Classical.choice/Quot.sound only. Regressions
cover exact values, zero reaction/extraction, a synthetic compatible-mass example
and counterexamples: negative kinetic energy violates the required work bound;
arbitrary independent masses need not have the supplied defect. The mass example
is artificial, not calibration. Full integrated scoped evidence is separate from
a new full beta. Initial import/tactic/format/test-syntax failures were retained.
The required source header was repaired during epsilon248 without mathematical edits.

Binary64 simulations are separate; correspondence to all Real formulas is unproved.
60fs,2T,mycelium or a fractal lattice do not supply dynamics, geometry or efficiency
in this model. Average power does not certify continuous supply. Thermodynamic
completeness, plasma stability, transport losses, fuel availability and autonomy
require additional evidence. The model checks dimensionally consistent budgets
with supplied coefficients; device application needs measured coefficient/design
links. Novelty not assessed; hardware admission, authorization and Third Obligation
remain unchanged.

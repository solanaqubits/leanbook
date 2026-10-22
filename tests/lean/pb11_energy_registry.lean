import Verification.MasterSuite

open PB11EnergyBalance

example : PB11EnergyBalanceSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).quantum_suite.pb11_energy
example (s : MasterSuite.QuantumPhysicsFullSuite) : PB11EnergyBalanceSuite := s.pb11_energy
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : PB11EnergyBalanceSuite :=
  s.quantum_physics_full_suite.pb11_energy
example (s : MasterSuite.QuantumPhysicsFullSuite) : electricalEnergy baseline = 1 / 8000 :=
  s.pb11_energy.output
example (s : MasterSuite.QuantumPhysicsFullSuite) (f w a p : ℝ) (hf : 0 ≤ f)
    (hw : 0 < w) (hw1 : w ≤ 1) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    netPower baseline f w a p ≤ 0 := s.pb11_energy.no_autonomy f w a p hf hw hw1 ha hp

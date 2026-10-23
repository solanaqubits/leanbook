import Verification.MasterSuite

open QuantumDiamondNVInterfaceContract

example : QuantumDiamondNVInterfaceSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.diamond_nv

example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumDiamondNVInterfaceSuite := s.quantum_physics_full_suite.diamond_nv

example (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1) (p : NVSpinPopulation) :
    (opticalPumpStep η hη p).p0 + (opticalPumpStep η hη p).pPlus +
      (opticalPumpStep η hη p).pMinus = 1 := (opticalPumpStep η hη p).h_sum_one

example (s : MasterSuite.QuantumPhysicsFullSuite) (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1)
    (k : ℕ) (p : NVSpinPopulation) :
    residual (pumpCycles η hη k p) = (1 - η) ^ k * residual p :=
  s.diamond_nv.finite_residual η hη k p

example (s : MasterSuite.QuantumPhysicsFullSuite) (η : ℚ) (hη : 0 ≤ η ∧ η ≤ 1)
    (hpos : 0 < η) (p : NVSpinPopulation) :
    Filter.Tendsto (fun k : ℕ => ((pumpCycles η hη k p).p0 : ℝ)) Filter.atTop (nhds 1) :=
  s.diamond_nv.pumping_limit η hη hpos p

example (s : MasterSuite.QuantumPhysicsFullSuite) (r0 rd : ℚ) (hr : rd < r0)
    (p q : NVSpinPopulation) :
    luminescenceYield r0 rd p < luminescenceYield r0 rd q ↔ p.p0 < q.p0 :=
  s.diamond_nv.strict_readout r0 rd hr p q

example (s : MasterSuite.QuantumPhysicsFullSuite) (a : CoherentAmp) (p : NVSpinPopulation)
    (h : Represents a p) : Represents (coherentPi a) (mwPiPulseStep p) :=
  s.diamond_nv.population_bridge a p h

import Verification.MasterSuite
open AlgebraQuaternionSpinor
example : QuaternionSpinorSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.quaternion_spinor
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : QuaternionSpinorSuite :=
  s.quantum_physics_full_suite.quaternion_spinor
example (s : MasterSuite.QuantumPhysicsFullSuite) (q : UnitQuat) (u v : Vec3) :
    dist (rotate q u) (rotate q v) = dist u v :=
  s.quaternion_spinor.euclidean_isometry q u v

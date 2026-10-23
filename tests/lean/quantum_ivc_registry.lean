import Verification.MasterSuite

open QuantumIVCAccumulatorContract

example : QuantumIVCAccumulatorSuite := by
  have s := MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}
  exact s.quantum_suite.quantum_ivc

example (s : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumIVCAccumulatorSuite := s.quantum_physics_full_suite.quantum_ivc

example (s : MasterSuite.QuantumPhysicsFullSuite) :
    QuantumIVCAccumulatorSuite := s.quantum_ivc

example (r : MasterSuite.QuantumPhysicsFullSuite) (a : IVCAccumulator)
    (ws : List StepWitness) :
    (foldSteps a ws).accumulatedFidelity = max 0 (a.accumulatedFidelity - totalLoss ws) :=
  r.quantum_ivc.exact_loss a ws

example (r : MasterSuite.QuantumPhysicsFullSuite) (a : IVCAccumulator)
    (ws : List StepWitness) (eps : ℚ) (he : 0 ≤ eps)
    (hw : ∀ w ∈ ws, w.fidelityLoss ≤ eps) :
    max 0 (a.accumulatedFidelity - (ws.length : ℚ) * eps) ≤
      (foldSteps a ws).accumulatedFidelity := r.quantum_ivc.linear_bound a ws eps he hw

example (r : MasterSuite.QuantumPhysicsFullSuite) (a : IVCAccumulator)
    (ws : List StepWitness) (h : a.allValid = false) :
    (foldSteps a ws).allValid = false := r.quantum_ivc.false_absorbing a ws h

example (r : MasterSuite.QuantumPhysicsFullSuite) (a : IVCAccumulator) (F : ℚ) :
    evalVerifierExpr a F verificationExpression = (verifyAccumulator a F, 3) :=
  r.quantum_ivc.symbolic_cost a F

example (r : MasterSuite.QuantumPhysicsFullSuite) (R : StepWitness → Prop)
    (a : IVCAccumulator) (ws : List StepWitness) (F : ℚ)
    (hR : ∀ w ∈ ws, w.valid = true → R w)
    (h : verifyAccumulator (foldSteps a ws) F = true) : ∀ w ∈ ws, R w :=
  r.quantum_ivc.semantic_soundness R a ws F hR h

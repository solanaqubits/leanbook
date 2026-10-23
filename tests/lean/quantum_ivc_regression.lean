import Verification.QuantumIVCAccumulatorContract

open QuantumIVCAccumulatorContract

private def zeroW : StepWitness := ⟨0, true, 0, by norm_num⟩
private def quarterW : StepWitness := ⟨9, true, 1 / 4, by norm_num⟩
private def halfW : StepWitness := ⟨2, true, 1 / 2, by norm_num⟩
private def badW : StepWitness := ⟨1, false, 0, by norm_num⟩
private def largeW : StepWitness := ⟨0, true, 2, by norm_num⟩
private def initialFalse : IVCAccumulator := ⟨7, false, 1, by norm_num, by norm_num⟩
private def halfAcc : IVCAccumulator := ⟨7, true, 1 / 2, by norm_num, by norm_num⟩
private def zeroAcc : IVCAccumulator := ⟨0, true, 0, by norm_num, by norm_num⟩

example : emptyAccumulator.totalSteps = 0 := rfl
example : emptyAccumulator.allValid = true := rfl
example : emptyAccumulator.accumulatedFidelity = 1 := rfl
example : verifyAccumulator emptyAccumulator 1 = true := empty_accumulator_valid _ (by norm_num)
example : verifyAccumulator emptyAccumulator 2 = false :=
  threshold_above_one_rejected _ _ (by norm_num)
example : verifyAccumulator emptyAccumulator (-1) = true := by
  norm_num [verifyAccumulator, emptyAccumulator]
example : foldSteps halfAcc [] = halfAcc := rfl
example : (foldStep emptyAccumulator quarterW).accumulatedFidelity = 3 / 4 := by
  norm_num [foldStep, emptyAccumulator, quarterW]
example : (foldStep halfAcc halfW).accumulatedFidelity = 0 := by
  norm_num [foldStep, halfAcc, halfW]
example : (foldStep emptyAccumulator largeW).accumulatedFidelity = 0 := by
  norm_num [foldStep, emptyAccumulator, largeW]
example : (foldStep zeroAcc quarterW).accumulatedFidelity = 0 := by
  norm_num [foldStep, zeroAcc, quarterW]
example : (foldStep halfAcc zeroW).accumulatedFidelity = halfAcc.accumulatedFidelity := by
  norm_num [foldStep, halfAcc, zeroW]
example : (foldStep halfAcc zeroW).totalSteps = 8 := rfl
example : (foldSteps emptyAccumulator [quarterW, halfW]).accumulatedFidelity = 1 / 4 := by
  norm_num [foldSteps, foldStep, emptyAccumulator, quarterW, halfW]
example : (foldSteps emptyAccumulator [quarterW, quarterW, quarterW]).accumulatedFidelity =
    1 / 4 := by norm_num [foldSteps, foldStep, emptyAccumulator, quarterW]
example : (foldSteps halfAcc [zeroW, quarterW]).totalSteps = 9 := rfl
example : (foldSteps emptyAccumulator [largeW, zeroW]).accumulatedFidelity = 0 := by
  norm_num [foldSteps, foldStep, emptyAccumulator, largeW, zeroW]
example : (foldSteps emptyAccumulator [zeroW, zeroW]).totalSteps = 2 := rfl
example : verifyAccumulator (foldSteps emptyAccumulator [zeroW, zeroW]) 1 = true := by
  norm_num [verifyAccumulator, foldSteps, foldStep, emptyAccumulator, zeroW]
-- Reversing nonsequential indices yields the same full summary.
example : foldSteps emptyAccumulator [quarterW, halfW] =
    foldSteps emptyAccumulator [halfW, quarterW] := by
  ext <;> norm_num [foldSteps, foldStep, emptyAccumulator, quarterW, halfW]
example (acc : IVCAccumulator) (w : StepWitness) :
    foldStep acc { w with stepIndex := 999 } = foldStep acc w := foldStep_index_independent _ _ _
example : (foldSteps emptyAccumulator [zeroW, badW, quarterW]).allValid = false := rfl
example : (foldSteps initialFalse [zeroW, quarterW]).allValid = false :=
  falsity_absorption _ _ rfl
example : verifyAccumulator (foldSteps emptyAccumulator [badW, zeroW]) (-100) = false := by
  norm_num [verifyAccumulator, foldSteps, foldStep, emptyAccumulator, badW, zeroW]
example : verifyAccumulator zeroAcc 0 = true := by norm_num [verifyAccumulator, zeroAcc]
example : verifyAccumulator zeroAcc (1 / 100) = false := by
  norm_num [verifyAccumulator, zeroAcc]
example : verifyAccumulator halfAcc (1 / 2) = true := by norm_num [verifyAccumulator, halfAcc]
example : verifyAccumulator halfAcc (3 / 4) = false := by norm_num [verifyAccumulator, halfAcc]
example : totalLoss [quarterW, halfW] = 3 / 4 := by norm_num [totalLoss, quarterW, halfW]
example (acc : IVCAccumulator) (ws : List StepWitness) :
    (foldSteps acc ws).accumulatedFidelity =
      max 0 (acc.accumulatedFidelity - totalLoss ws) := exact_fidelity_after_fold _ _
example : max 0 (1 - (3 : ℚ) * (1 / 4)) ≤
    (foldSteps emptyAccumulator [quarterW, quarterW, quarterW]).accumulatedFidelity := by
  norm_num [foldSteps, foldStep, emptyAccumulator, quarterW]
example (acc : IVCAccumulator) (ws : List StepWitness) (eps : ℚ) (he : 0 ≤ eps)
    (hw : ∀ w ∈ ws, w.fidelityLoss ≤ eps) :
    max 0 (acc.accumulatedFidelity - (ws.length : ℚ) * eps) ≤
      (foldSteps acc ws).accumulatedFidelity := linear_fidelity_lower_bound _ _ _ he hw
-- Acceptance alone does not authenticate even a simple index predicate.
example : verifyAccumulator (foldSteps emptyAccumulator [zeroW]) 1 = true ∧
    ¬ zeroW.stepIndex = 1 := by
  norm_num [verifyAccumulator, foldSteps, foldStep, emptyAccumulator, zeroW]
example (acc : IVCAccumulator) (ws : List StepWitness) (Fmin : ℚ)
    (ha : verifyAccumulator (foldSteps acc ws) Fmin = true) : ∀ w ∈ ws, 0 ≤ w.fidelityLoss :=
  conditional_semantic_soundness (fun w => 0 ≤ w.fidelityLoss) acc ws Fmin
    (fun w _ _ => w.h_loss_nonneg) ha
example : evalVerifierExpr emptyAccumulator 1 .ReadValid = (true, 1) := rfl
example : evalVerifierExpr emptyAccumulator 2 .FidelityCompare = (false, 1) := by
  norm_num [evalVerifierExpr, emptyAccumulator]
example : evalVerifierExpr emptyAccumulator 1 verificationExpression = (true, 3) := by
  norm_num [evalVerifierExpr, verificationExpression, emptyAccumulator]
-- A false left operand still incurs both subexpression costs in the eager model.
example : evalVerifierExpr initialFalse 1 verificationExpression = (false, 3) := rfl
example : evalVerifierExpr emptyAccumulator 1
    (.And (.And .ReadValid .ReadValid) .FidelityCompare) = (true, 5) := by
  norm_num [evalVerifierExpr, emptyAccumulator]
example (acc : IVCAccumulator) (Fmin : ℚ) :
    evalVerifierExpr acc Fmin verificationExpression = (verifyAccumulator acc Fmin, 3) :=
  verification_constant_time_model _ _
example : (evalVerifierExpr halfAcc 0 verificationExpression).2 =
    (evalVerifierExpr emptyAccumulator 100 verificationExpression).2 := rfl
example : ¬ (0 : ℚ) ≤ -1 := by norm_num
example : QuantumIVCAccumulatorSuite := verification_suite

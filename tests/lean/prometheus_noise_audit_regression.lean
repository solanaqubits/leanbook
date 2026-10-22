import Verification.PrometheusNoiseAudit

open PrometheusNoiseAudit

-- API applications and independent expected boundaries for the deterministic model.
example : residualEnergy 1 1 4 0 = 4 := residual_initial _ _ _ (by norm_num)
example : stoppingRange 1 1 1 = Real.log 2 := by norm_num [stoppingRange]
example : residualEnergy 1 1 1 (Real.log 2) = 0 := by
  apply residual_zero_at_or_after_range <;> norm_num [stoppingRange]
example : 0 < residualEnergy 1 1 1 0 := by norm_num [residualEnergy]
example : residualEnergy 1 1 1 0 ≠ 0 := by norm_num [residualEnergy]
example (X : ℝ) (h : stoppingRange 1 1 2 < X) :
    ∃ Xstop, 0 < Xstop ∧ Xstop < X ∧ residualEnergy 1 1 1 Xstop = 0 ∧
      residualEnergy 1 1 1 X = 0 :=
  stopped_before_detector 1 1 1 2 X (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) h
example : massThickness 3 10 = 30 := by norm_num [massThickness]
example : ∃ g : Geometry, g.signalChord ≠ g.shieldLength 0 := by
  refine ⟨⟨10, fun _ => 1, by norm_num, fun _ => by norm_num⟩, ?_⟩
  norm_num

-- Nonzero false alarms; strict improvement depends on positive probabilities below one.
example : independentFPR (1 / 100) (1 / 100) = 1 / 10000 := explicit_single_window.1
example : independentFPR (1 / 100) (1 / 100) ≠ 0 := ne_of_gt explicit_single_window.2
example : 0 < independentFPR (1 / 100) (1 / 100) ∧
    independentFPR (1 / 100) (1 / 100) < min (1 / 100) (1 / 100) := by
  exact factorized_joint_bounds _ _ _ (by norm_num) (by norm_num) rfl
example : ¬independentFPR 0 (1 / 100) < min 0 (1 / 100) := by norm_num [independentFPR]
example : independentFPR 1 (1 / 100) = min 1 (1 / 100) := by norm_num [independentFPR]
example : commonCauseFPR (1 / 10) (1 / 100) (1 / 100) = 10009 / 100000 := by
  norm_num [commonCauseFPR, independentFPR]
-- Perfectly correlated .01 marginals admit .01 joint probability: not a product.
example : (1 / 100 : ℝ) ≠ independentFPR (1 / 100) (1 / 100) := by norm_num [independentFPR]
example : 0 < iidAnyFalseAlarm (1 / 10000) 10000 := explicit_many_windows
example : iidAnyFalseAlarm (1 / 10000) 0 = 0 := by simp [iidAnyFalseAlarm]
example : iidAnyFalseAlarm 0 10000 = 0 := by simp [iidAnyFalseAlarm]

example : receive false (some false) = none := rfl
example : receive true none = none := rfl
example : receive true (some false) = some false := rfl
example : classify (.signal false) (some false) = .correct := rfl
example : classify (.signal true) (some false) = .substitution := rfl
example : classify (.signal false) none = .erasure := rfl
example : classify .noSignal (some false) = .falseAlarm := rfl
example : classify .noSignal none = .rejectedBackground := rfl
example : evaluate .noSignal true none = .falseAlarm := rfl
example : evaluate .noSignal false (some false) = .rejectedBackground := rfl
example : evaluate (.signal false) false (some false) = .erasure := rfl
example : evaluate (.signal false) true none = .erasure := rfl
example : evaluate (.signal false) true (some false) = .correct := rfl
example : evaluate (.signal true) true (some false) = .substitution := rfl

-- A concrete normalized outcome distribution: differing denominators matter.
noncomputable def auditMass : OutcomeMass :=
  ⟨1 / 4, 1 / 8, 1 / 8, 1 / 10, 2 / 5, by norm_num, by norm_num⟩

example : erasureRate auditMass = 1 / 4 := by norm_num [erasureRate, signalMass, auditMass]
example : deliveredBER auditMass = 1 / 3 := by norm_num [deliveredBER, deliveredMass, auditMass]
example : falseAlarmRate auditMass = 1 / 5 := by norm_num [falseAlarmRate, signalMass, auditMass]
example : totalFailureMass auditMass = 7 / 20 := by norm_num [totalFailureMass, auditMass]
example : totalFailureMass auditMass ≠
    erasureRate auditMass + deliveredBER auditMass + falseAlarmRate auditMass := by
  norm_num [totalFailureMass, erasureRate, deliveredBER, falseAlarmRate, signalMass,
    deliveredMass, auditMass]
example : totalFailureMass auditMass = signalMass auditMass *
    (erasureRate auditMass + (1 - erasureRate auditMass) * deliveredBER auditMass) +
    (1 - signalMass auditMass) * falseAlarmRate auditMass := by
  apply total_error_decomposition <;> norm_num [signalMass, deliveredMass, auditMass]

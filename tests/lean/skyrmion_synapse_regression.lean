import Verification.SpintronicSkyrmionSynapseContract

open SpintronicSkyrmionSynapseContract
open PulseAction

private def empty3 : SkyrmionSynapse 3 := ⟨0, by decide⟩
private def one3 : SkyrmionSynapse 3 := ⟨1, by decide⟩
private def two3 : SkyrmionSynapse 3 := ⟨2, by decide⟩
private def full3 : SkyrmionSynapse 3 := ⟨3, by decide⟩

example : weight one3 = (1 / 3 : ℚ) := by norm_num [weight, one3]
example {N : ℕ} (hN : 0 < N) (s : SkyrmionSynapse N) :
    0 ≤ weight s ∧ weight s ≤ 1 := weight_in_unit_interval hN s

-- Threshold equality is active, while both nearby interior currents are inactive.
example : classifyCurrent 1 1 = Potentiate := by norm_num [classifyCurrent]
example : classifyCurrent 1 (-1) = Depress := by norm_num [classifyCurrent]
example : classifyCurrent 1 (999 / 1000) = Subthreshold := by norm_num [classifyCurrent]
example : classifyCurrent 1 (-999 / 1000) = Subthreshold := by norm_num [classifyCurrent]
example : classifyCurrent 1 (3 / 2) = Potentiate := by norm_num [classifyCurrent]
example : classifyCurrent 1 (-3 / 2) = Depress := by norm_num [classifyCurrent]
example (threshold : ℚ) (ht : 0 < threshold) : classifyCurrent threshold 0 = Subthreshold :=
  classify_zero threshold ht

-- Invalid threshold choices must not inherit the positive-threshold theorem.
example : classifyCurrent 0 0 = Potentiate := by norm_num [classifyCurrent]
example : classifyCurrent (-1) 0 = Potentiate := by norm_num [classifyCurrent]
example : stateUpdate 0 0 empty3 ≠ empty3 := by
  intro h
  have hc := congrArg SkyrmionSynapse.count h
  norm_num [stateUpdate, classifyCurrent, step, empty3] at hc

example : (step Potentiate one3).count = 2 := by norm_num [step, one3]
example : (step Potentiate full3).count = 3 := by norm_num [step, full3]
example : (step Depress two3).count = 1 := by norm_num [step, two3]
example : (step Depress empty3).count = 0 := by norm_num [step, empty3]
example : step Subthreshold one3 = one3 := rfl
example : stateUpdate 1 0 one3 = one3 := zero_current_invariance 1 (by norm_num) one3
example : (stateUpdate 1 1 one3).count = 2 := by
  norm_num [stateUpdate, classifyCurrent, step, one3]
example : (stateUpdate 1 (-1) one3).count = 0 := by
  norm_num [stateUpdate, classifyCurrent, step, one3]

example (a : PulseAction) {N : ℕ} (s : SkyrmionSynapse N) : repeatPulse a 0 s = s := rfl
example : (repeatPulse Potentiate 2 one3).count = 3 := by
  rw [repeat_potentiate_count]
  norm_num [one3]
example : (repeatPulse Depress 2 full3).count = 1 := by
  rw [repeat_depress_count]
  norm_num [full3]
example : (repeatPulse Potentiate 1000 empty3).count = 3 ∧
    weight (repeatPulse Potentiate 1000 empty3) = 1 :=
  saturation_by_dose_potentiate (by decide) 1000 empty3 (by decide)
example : (repeatPulse Depress 1000 full3).count = 0 ∧
    weight (repeatPulse Depress 1000 full3) = 0 :=
  saturation_by_dose_depress 1000 full3 (by decide)

-- Sharp dose: two events suffice from one3; one event does not.
example (k : ℕ) : (repeatPulse Potentiate k one3).count = 3 ↔ 2 ≤ k := by
  simpa [one3] using potentiation_saturated_iff k one3
example : (repeatPulse Potentiate 1 one3).count ≠ 3 := by
  rw [repeat_potentiate_count]
  norm_num [one3]
example (k : ℕ) : (repeatPulse Depress k two3).count = 0 ↔ 2 ≤ k := by
  simpa [two3] using depression_saturated_iff k two3
example {N : ℕ} (hN : 0 < N) (s : SkyrmionSynapse N) :
    weight s ≤ weight (step Potentiate s) := step_monotonicity_potentiate hN s
example {N : ℕ} (hN : 0 < N) (s : SkyrmionSynapse N) :
    weight (step Depress s) ≤ weight s := step_monotonicity_depress hN s
example : weight (step Potentiate full3) = weight full3 := by norm_num [weight, step, full3]

-- Smallest positive capacity and the separate degenerate N=0 domain.
example : weight (step Potentiate (⟨0, by decide⟩ : SkyrmionSynapse 1)) = 1 := by
  norm_num [weight, step]
example : weight (step Depress (⟨1, by decide⟩ : SkyrmionSynapse 1)) = 0 := by
  norm_num [weight, step]
example (a : PulseAction) (s : SkyrmionSynapse 0) : step a s = s := by
  apply SkyrmionSynapse.ext
  have hc : s.count = 0 := by have := s.h_le; omega
  cases a <;> simp [step, hc]
example (k : ℕ) (s : SkyrmionSynapse 0) : weight (repeatPulse Potentiate k s) ≠ 1 := by
  rw [weight_zero_capacity]
  norm_num

example : repeatPulse (classifyCurrent 1 (1 / 2)) 1000 one3 = one3 :=
  repeated_subthreshold_memory 1 (1 / 2) 1000 one3 (by norm_num)
example : stateUpdate 1 ((3 / 4) + (1 / 8)) one3 = one3 :=
  bounded_disturbance_invariance 1 (3 / 4) (1 / 8) one3 (by norm_num)

-- A non-strict disturbance margin can land exactly on the active endpoint.
example : stateUpdate 1 ((1 / 2) + (1 / 2)) empty3 ≠ empty3 := by
  intro h
  have hc := congrArg SkyrmionSynapse.count h
  norm_num [stateUpdate, classifyCurrent, step, empty3] at hc

-- Homogeneous-dose results do not commute arbitrary mixed event sequences.
example : step Depress (step Potentiate empty3) ≠ step Potentiate (step Depress empty3) := by
  intro h
  have hc := congrArg SkyrmionSynapse.count h
  norm_num [step, empty3] at hc

example : step Depress full3 ≠ full3 := by
  intro h
  have hc := congrArg SkyrmionSynapse.count h
  norm_num [step, full3] at hc

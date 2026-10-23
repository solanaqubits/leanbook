import Verification.DataAvailabilitySamplingContract

open DataAvailabilitySamplingContract

private def small : RSBlockParams := ⟨1, 2, by decide, by decide⟩
private def four : RSBlockParams := ⟨2, 4, by decide, by decide⟩
private def large : RSBlockParams := ⟨100, 200, by decide, by decide⟩
private def noneAvailable : BlockAvailabilityState four := ⟨0, by decide⟩
private def oneAvailable : BlockAvailabilityState four := ⟨1, by decide⟩
private def thresholdAvailable : BlockAvailabilityState four := ⟨2, by decide⟩
private def allAvailable : BlockAvailabilityState four := ⟨4, by decide⟩
private def one : Finset (Fin 4) := {0}
private def two : Finset (Fin 4) := {0, 1}

example : ¬ isRecoverable four noneAvailable := by norm_num [isRecoverable, four, noneAvailable]
example : ¬ isRecoverable four oneAvailable := by norm_num [isRecoverable, four, oneAvailable]
example : isRecoverable four thresholdAvailable := by norm_num [isRecoverable, four, thresholdAvailable]
example : isRecoverable four allAvailable := by norm_num [isRecoverable, four, allAvailable]
example : four.n - oneAvailable.availableShards = 3 := rfl
example : ¬ four.k < four.n - thresholdAvailable.availableShards := by decide
example : isRecoverable small ⟨1, by decide⟩ := by norm_num [isRecoverable, small]
example : ¬ isRecoverable small ⟨0, by decide⟩ := by norm_num [isRecoverable, small]
example : Fintype.card (SamplingTrace 4 2) = 16 := by rw [all_trace_count]; norm_num
example : Fintype.card (SuccessfulTrace one 2) = 1 := by
  rw [successful_trace_count]; norm_num [one]
example : Fintype.card (SuccessfulTrace two 2) = 4 := by
  rw [successful_trace_count]; norm_num [two]
example : Fintype.card (SuccessfulTrace (∅ : Finset (Fin 2)) 0) = 1 := by
  rw [successful_trace_count]; norm_num
example : Fintype.card (SuccessfulTrace (∅ : Finset (Fin 2)) 1) = 0 := by
  rw [successful_trace_count]; norm_num
example : samplingSuccessProbability one 0 = 1 := by
  rw [sampling_probability_formula]; norm_num
example : samplingSuccessProbability (∅ : Finset (Fin 2)) 0 = 1 := by
  rw [sampling_probability_formula]; norm_num
example : samplingSuccessProbability (∅ : Finset (Fin 2)) 1 = 0 := by
  rw [sampling_probability_formula]; norm_num
example : samplingSuccessProbability one 1 = 1 / 4 := by
  rw [sampling_probability_formula]; norm_num [one]
example : samplingSuccessProbability one 2 = 1 / 16 := by
  rw [sampling_probability_formula]; norm_num [one]
example : samplingSuccessProbability two 2 = 1 / 4 := by
  rw [sampling_probability_formula]; norm_num [two]
example : samplingSuccessProbability (Finset.univ : Finset (Fin 4)) 20 = 1 := by
  rw [sampling_probability_formula]; norm_num
example : maxDeceptionProbability four 0 = 1 := by norm_num [maxDeceptionProbability]
example : maxDeceptionProbability four 1 = 1 / 2 := by norm_num [maxDeceptionProbability]
example : maxDeceptionProbability four 20 = 1 / 1048576 :=
  (sampling_security_exponential_bound four).1
example : maxDeceptionProbability four 20 < 1 / 1000000 :=
  (sampling_security_exponential_bound four).2
example : samplingSuccessProbability one 20 < 1 / 1000000 :=
  twenty_sample_security four one (by change one.card < 2; norm_num [one])
example : maxDeceptionProbability small 20 = maxDeceptionProbability large 20 := rfl
example : Fintype.card (Fin 20) = 20 ∧ Fintype.card (Fin 20) < large.n ∧
    maxDeceptionProbability large 20 < 1 / 1000000 :=
  light_client_verification_model large (by decide)
example : ¬ 20 < small.n := by decide
example : ¬ 20 < four.k := by decide
example : 20 < large.k := by decide
example (S : ℕ) : samplingSuccessProbability one (S + 1) ≤ samplingSuccessProbability one S :=
  sampling_probability_antitone (by decide : 0 < 4) one (Nat.le_succ S)
-- Sampling with replacement permits all twenty positions to repeat one available shard.
example : ∃ t : SuccessfulTrace one 20, ∀ i, t.1 i = 0 := by
  refine ⟨⟨fun _ => 0, fun _ => by simp [one]⟩, ?_⟩
  intro i; rfl
-- A different sampling law: one uniform seed reused for three positions.
private def repeatedSeedSuccess : Finset (Fin 4) :=
  Finset.univ.filter (fun seed => ∀ _i : Fin 3, seed ∈ one)
private def correlatedProbability : ℚ := (repeatedSeedSuccess.card : ℚ) / 4
example : repeatedSeedSuccess.card = 1 := by decide
example : correlatedProbability = 1 / 4 := by
  have hc : repeatedSeedSuccess.card = 1 := by decide
  norm_num [correlatedProbability, hc]
example : samplingSuccessProbability one 3 < correlatedProbability := by
  have hc : repeatedSeedSuccess.card = 1 := by decide
  rw [sampling_probability_formula]
  norm_num [one, correlatedProbability, hc]
example : correlatedProbability > maxDeceptionProbability four 3 := by
  have hc : repeatedSeedSuccess.card = 1 := by decide
  norm_num [correlatedProbability, hc, maxDeceptionProbability]
example : ¬ ((0 : ℕ) > 0) := by decide
example : isRecoverable four (stateOfAvailable four two) := by
  change 2 ≤ two.card
  norm_num [two]
example : ¬ isRecoverable four (stateOfAvailable four one) := by
  change ¬ 2 ≤ one.card
  norm_num [one]
example : Lagrange.interpolate two (fun i : Fin 4 => (i.val : ℚ)) (fun _ => 7) =
    Polynomial.C 7 := by
  refine recoverable_polynomial_reconstruction four two
    (fun i : Fin 4 => (i.val : ℚ)) (fun _ => 7) ?_ (Polynomial.C 7) ?_ ?_ ?_
  · intro i _ j _ hij
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at hij
    exact_mod_cast hij
  · norm_num [four, Polynomial.degree_C]
  · intro i _
    simp
  · change 2 ≤ two.card
    norm_num [two]
example : ∃ p q : Polynomial ℚ, p ≠ q ∧ p.degree < 2 ∧ q.degree < 2 ∧
    ∀ i ∈ one, p.eval (i.val : ℚ) = q.eval (i.val : ℚ) :=
  shortage_two_polynomials one (fun i : Fin 4 => (i.val : ℚ)) 2 (by norm_num [one])
-- Repeated evaluation nodes cannot distinguish zero from X, regardless of index count.
example : (0 : Polynomial ℚ) ≠ Polynomial.X ∧
    ∀ i ∈ two, (0 : Polynomial ℚ).eval (0 : ℚ) = Polynomial.X.eval (0 : ℚ) := by
  exact ⟨Ne.symm Polynomial.X_ne_zero, by simp⟩
example : DataAvailabilitySamplingSuite := verification_suite

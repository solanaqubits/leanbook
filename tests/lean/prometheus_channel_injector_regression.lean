import Verification.PrometheusChannelAndInjectorAudit

open PrometheusChannelAndInjectorAudit

-- Exact input interpretation: substitution frequency is conditional on delivery.
example : observedSubstitution = 17 / 1668 := by norm_num [observedSubstitution]
example : observedSubstitution ≠ 34 / 10000 := by norm_num [observedSubstitution]
example : transition observedErasure observedSubstitution false .one = 17 / 5000 := by
  norm_num [transition, observedErasure, observedSubstitution]
example : 0 < transition observedErasure observedSubstitution false .one := by
  norm_num [transition, observedErasure, observedSubstitution]
example : 1 - observedErasure = observedDelivery := delivery_fraction
example : 1 / 3 < observedDelivery := delivery_above_third

-- Independent numerical transition-row and output-marginal expectations.
example : transition (1 / 2) (1 / 4) false .erased = 1 / 2 := rfl
example : transition (1 / 2) (1 / 4) false .zero = 3 / 8 := by norm_num [transition]
example : transition (1 / 2) (1 / 4) false .one = 1 / 8 := by norm_num [transition]
example : transition (1 / 2) (1 / 4) true .zero = 1 / 8 := by norm_num [transition]
example : transition (1 / 2) (1 / 4) true .one = 3 / 8 := by norm_num [transition]
example : uniformOutputMass (1 / 2) (1 / 4) .one = 1 / 4 := by
  rw [uniform_output_one]
  norm_num
example (sent : Bool) : sumOutputs (transition (1 / 2) (1 / 4) sent) = 1 :=
  transition_normalized _ _ sent
example : 0 ≤ transition 1 0 false .zero := transition_nonnegative _ _
  (by norm_num) (by norm_num) _ _
example : transition 2 0 false .zero < 0 := by norm_num [transition]
example : uniformMutualInformation observedErasure observedSubstitution = observedCapacity := by
  apply uniform_information_formula <;> norm_num [observedErasure, observedSubstitution]

-- Genuine entropy values/bounds, including boundary checks.
example : binaryEntropy 0 = 0 := by simp [binaryEntropy]
example : binaryEntropy 1 = 0 := by simp [binaryEntropy]
example : binaryEntropy (1 / 2) = 1 := by
  have hl : Real.log (1 / 2) = -Real.log 2 := by
    simp
  norm_num [binaryEntropy]
  rw [hl]
  field_simp [ne_of_gt log_two_positive]
  ring
example : binaryEntropy observedSubstitution < 9 / 100 := observed_entropy_lt_nine_percent
example : 0 < binaryEntropy observedSubstitution := observed_entropy_positive
example : binaryEntropy observedSubstitution ≤ 1 :=
  binary_entropy_le_one _ (by norm_num [observedSubstitution])
example (bias : ℝ) (hb₀ : 0 ≤ bias) (hb₁ : bias ≤ 1) :
    mutualInformation observedErasure observedSubstitution bias ≤ observedCapacity := by
  exact information_le_capacity _ _ _ (by norm_num [observedErasure])
    (by norm_num [observedSubstitution]) ⟨hb₀, hb₁⟩
example : mutualInformation observedErasure observedSubstitution (1 / 2) = observedCapacity := by
  exact information_uniform_attains _ _ (by norm_num [observedErasure])
    (by norm_num [observedSubstitution])
example : mutualInformation observedErasure observedSubstitution 0 = 0 := by
  rw [information_formula _ _ _ (by norm_num [observedErasure])
    (by norm_num [observedSubstitution]) (by norm_num)]
  simp [outputBias]
example : idealCapacity (1 / 2) (1 / 2) = 0 := by
  rw [idealCapacity, binary_entropy_half]
  ring
example : 3 / 10 < observedCapacity := observed_capacity_lower
example : observedCapacity < 1 := observed_capacity_upper
example : codeRate 3000 10000 < observedCapacity :=
  conditional_rate_budget _ _ (by norm_num) (by norm_num)
example : codeRate 1000 10000 < observedCapacity :=
  conditional_rate_budget _ _ (by norm_num) (by norm_num)
example : Function.Injective identityEncoder := identity_encoder_injective
example : observedCapacity < codeRate 1 1 := identity_code_above_capacity
example : identityDecoder (fun _ => true) ≠ (fun _ : Fin 1 => false) := identity_code_flip_error
example : ¬(∀ k n : ℕ, 0 < n → k ≤ n → codeRate k n ≤ observedCapacity) :=
  not_every_finite_rate_below_capacity
example : codeRate 1 1 ≤ ((1 / 2 : ℝ) + 1 / 1) / (1 - 1 / 4) := by
  simpa using conditional_fano_rate_bound 1 1 (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num)

-- 10 ns = 1/100000 ms; the block adds 0.1 ms at 10000 uses.
example : totalLatencyMs 10000 1 = 4151 / 100 := by norm_num [totalLatencyMs]
example : roundedFiberMs - totalLatencyMs 10000 1 = 36411 / 1000 := by
  norm_num [roundedFiberMs, totalLatencyMs]
example : 36 < roundedFiberMs - totalLatencyMs 10000 1 := by
  have := latency_gap 10000 1 (by norm_num) (by norm_num)
  linarith
example : ¬totalLatencyMs 10000 100 < roundedFiberMs := by
  norm_num [totalLatencyMs, roundedFiberMs]
example : ¬totalLatencyMs 10000000 1 < roundedFiberMs := by
  norm_num [totalLatencyMs, roundedFiberMs]

-- Kinetic-energy bookkeeping, not total fusion yield or wall-plug gain.
example : injectorNeutronKineticJ = 117759982599 / 100000000000000000 := neutron_kinetic_exact
example : injectorNeutronKineticJ < 11776 / 10000000000 := neutron_kinetic_bracket.2
example : injectorNeutronKineticJ ≠ 11776 / 10000000000 := ne_of_lt neutron_kinetic_bracket.2
example : neutronKineticFraction = 117759982599 / 160000000000000000 := by
  norm_num [neutronKineticFraction, incidentLaserJ, injectorNeutronKineticJ, joulePerMeV]
example : neutronKineticFraction < 1 / 100000 := neutron_fraction_bounds.2.1
example : neutronKineticFraction < 1 := neutron_fraction_bounds.2.2

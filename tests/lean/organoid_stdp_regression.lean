import Verification.BiohybridOrganoidSynapseContract
import Mathlib.Algebra.BigOperators.Fin

open BiohybridOrganoidSynapseContract

private def unitParams : STDPParameters :=
  ⟨1, 1, 1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩
private def asymmetricParams : STDPParameters :=
  ⟨2, 3, 2, 4, by norm_num, by norm_num, by norm_num, by norm_num⟩
private def zeroState : OrganoidSynapseState :=
  ⟨0, 1, by norm_num, by norm_num, by norm_num⟩
private def halfState : OrganoidSynapseState :=
  ⟨1 / 2, 1, by norm_num, by norm_num, by norm_num⟩
private def fullState : OrganoidSynapseState :=
  ⟨1, 1, by norm_num, by norm_num, by norm_num⟩
private def smallCap : OrganoidSynapseState :=
  ⟨1 / 4, 1 / 3, by norm_num, by norm_num, by norm_num⟩
private def pairStates : EnsembleState 2 := fun i => if i = 0 then halfState else fullState
private def twoHalves : EnsembleState 2 := fun _ => halfState
private def twoZeros : EnsembleState 2 := fun _ => zeroState
private def emptyEnsemble : EnsembleState 0 := Fin.elim0

example : stdpWindow unitParams 1 = 1 / 2 := by norm_num [stdpWindow, unitParams]
example : stdpWindow unitParams (-1) = -1 / 2 := by norm_num [stdpWindow, unitParams]
example : stdpWindow asymmetricParams 2 = 1 := by norm_num [stdpWindow, asymmetricParams]
example : stdpWindow asymmetricParams (-2) = -2 := by norm_num [stdpWindow, asymmetricParams]
example : stdpWindow asymmetricParams 2 ≠ -stdpWindow asymmetricParams (-2) := by
  norm_num [stdpWindow, asymmetricParams]
example (p : STDPParameters) : stdpWindow p 0 = 0 := stdp_window_zero p
example (p : STDPParameters) (dt : ℤ) :
    (stdpWindow p dt = 0 ↔ dt = 0) := (stdp_asymmetry_sign p dt).2.2

example : (stdpUpdate unitParams halfState 1).weight = 1 := by
  norm_num [stdpUpdate, stdpWindow, unitParams, halfState]
example : (stdpUpdate unitParams halfState (-1)).weight = 0 := by
  norm_num [stdpUpdate, stdpWindow, unitParams, halfState]
example : (stdpUpdate unitParams smallCap 1).weight = 1 / 3 := by
  norm_num [stdpUpdate, stdpWindow, unitParams, smallCap]
example : (stdpUpdate unitParams smallCap 1).wMax = 1 / 3 := rfl
example : 0 < stdpWindow unitParams 1 ∧
    (stdpUpdate unitParams fullState 1).weight - fullState.weight = 0 := by
  norm_num [stdpWindow, stdpUpdate, unitParams, fullState]
example : stdpWindow unitParams (-1) < 0 ∧
    (stdpUpdate unitParams zeroState (-1)).weight - zeroState.weight = 0 := by
  norm_num [stdpWindow, stdpUpdate, unitParams, zeroState]
example (p : STDPParameters) (s : OrganoidSynapseState) : stdpUpdate p s 0 = s :=
  stdp_zero_identity p s
example (p : STDPParameters) (s : OrganoidSynapseState) : eventUpdate p s none = s :=
  silence_invariance p s
example (p : STDPParameters) (s : OrganoidSynapseState) : eventUpdate p s (some 0) = s :=
  zero_event_identity p s
example : (none : Option ℤ) ≠ some 0 := by decide

example : totalWeight pairStates = 3 / 2 := by
  norm_num [totalWeight, Fin.sum_univ_two, pairStates, halfState, fullState]
example : normalizationFactor 1 pairStates = 2 / 3 := by
  norm_num [normalizationFactor, totalWeight, Fin.sum_univ_two, pairStates,
    halfState, fullState]
example : (homeostaticNormalize 1 (by norm_num) pairStates 0).weight = 1 / 3 ∧
    (homeostaticNormalize 1 (by norm_num) pairStates 1).weight = 2 / 3 := by
  norm_num [homeostaticNormalize, normalizationFactor, totalWeight, Fin.sum_univ_two,
    pairStates, halfState, fullState]
example : totalWeight (homeostaticNormalize 1 (by norm_num) pairStates) = 1 := by
  rw [total_after_normalize]
  norm_num [totalWeight, Fin.sum_univ_two, pairStates, halfState, fullState]
example : homeostaticNormalize 2 (by norm_num) pairStates = pairStates := by
  apply normalize_if_within_budget
  norm_num [totalWeight, Fin.sum_univ_two, pairStates, halfState, fullState]
example : homeostaticNormalize (3 / 2) (by norm_num) pairStates = pairStates := by
  apply normalize_if_within_budget
  norm_num [totalWeight, Fin.sum_univ_two, pairStates, halfState, fullState]
example (i : Fin 2) : (homeostaticNormalize 0 (by norm_num) pairStates i).weight = 0 := by
  norm_num [homeostaticNormalize, normalizationFactor, totalWeight, Fin.sum_univ_two,
    pairStates, halfState, fullState]
example : normalizationFactor 0 twoZeros = 1 := by
  norm_num [normalizationFactor, totalWeight, Fin.sum_univ_two, twoZeros, zeroState]
example : homeostaticNormalize 0 (by norm_num) twoZeros = twoZeros := by
  apply normalize_if_within_budget
  norm_num [totalWeight, Fin.sum_univ_two, twoZeros, zeroState]
example : totalWeight emptyEnsemble = 0 := by simp [totalWeight]
example : totalWeight (homeostaticNormalize 0 (by norm_num) emptyEnsemble) = 0 := by
  simp [totalWeight]
example : ¬ totalWeight emptyEnsemble ≤ (-1 : ℚ) := by simp [totalWeight]
example : ¬ (0 ≤ (-1 : ℚ)) := by norm_num
example : homeostaticNormalize 1 (by norm_num) (homeostaticNormalize 1 (by norm_num) pairStates) =
    homeostaticNormalize 1 (by norm_num) pairStates := normalization_idempotent _ _ _
example (i j : Fin 2) :
    (homeostaticNormalize 1 (by norm_num) pairStates i).weight * (pairStates j).weight =
      (homeostaticNormalize 1 (by norm_num) pairStates j).weight * (pairStates i).weight :=
  normalization_cross_ratio _ _ _ _ _

example : ensembleStep unitParams 1 (by norm_num) twoHalves (fun _ => none) = twoHalves := by
  apply composite_silence_invariance
  · intro i; rfl
  · norm_num [totalWeight, Fin.sum_univ_two, twoHalves, halfState]

-- Full silence does not suppress normalization of an initially over-budget ensemble.
example : (ensembleStep unitParams 1 (by norm_num) pairStates (fun _ => none) 0).weight = 1 / 3 := by
  norm_num [ensembleStep, ensembleEventUpdate, eventUpdate, homeostaticNormalize,
    normalizationFactor, totalWeight, Fin.sum_univ_two, pairStates, halfState, fullState]
example : ensembleStep unitParams 1 (by norm_num) pairStates (fun _ => none) ≠ pairStates := by
  intro h
  have hw := congrArg (fun s : EnsembleState 2 => (s 0).weight) h
  norm_num [ensembleStep, ensembleEventUpdate, eventUpdate, homeostaticNormalize,
    normalizationFactor, totalWeight, Fin.sum_univ_two, pairStates, halfState, fullState] at hw

-- A silent coordinate can decrease because another coordinate is potentiated.
example : (ensembleStep unitParams 1 (by norm_num) twoHalves
    (fun i => if i = 0 then none else some 1) 0).weight = 1 / 3 := by
  norm_num [ensembleStep, ensembleEventUpdate, eventUpdate, homeostaticNormalize,
    normalizationFactor, totalWeight, Fin.sum_univ_two, twoHalves, halfState,
    stdpUpdate, stdpWindow, unitParams]

-- Both local events are LTP, yet the first final weight falls from1/2 to3/8.
example : (ensembleEventUpdate unitParams twoHalves
    (fun i => if i = 0 then some 9 else some 1) 0).weight = 3 / 5 ∧
    (ensembleStep unitParams 1 (by norm_num) twoHalves
      (fun i => if i = 0 then some 9 else some 1) 0).weight = 3 / 8 ∧
    (ensembleStep unitParams 1 (by norm_num) twoHalves
      (fun i => if i = 0 then some 9 else some 1) 1).weight = 5 / 8 := by
  norm_num [ensembleStep, ensembleEventUpdate, eventUpdate, homeostaticNormalize,
    normalizationFactor, totalWeight, Fin.sum_univ_two, twoHalves, halfState,
    stdpUpdate, stdpWindow, unitParams]

example (events : Fin 2 → Option ℤ) :
    totalWeight (ensembleStep unitParams 1 (by norm_num) twoHalves events) ≤ 1 :=
  ensemble_budget_bound _ _ _ _ _
example (events : Fin 2 → Option ℤ) (i : Fin 2) :
    (ensembleStep unitParams 1 (by norm_num) twoHalves events i).wMax = (twoHalves i).wMax :=
  ensemble_wMax _ _ _ _ _ _

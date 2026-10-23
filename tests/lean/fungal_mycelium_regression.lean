import Verification.FungalMyceliumMemristorContract

open FungalMyceliumMemristorContract

private def halfParams : MemristorParameters :=
  ⟨1, 3, 2, 1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩
private def fullParams : MemristorParameters :=
  ⟨1, 3, 2, 1, 1, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩
private def mid : MemristorState halfParams := ⟨2, by norm_num [halfParams],
  by norm_num [halfParams]⟩
private def low : MemristorState halfParams := ⟨1, by norm_num [halfParams],
  by norm_num [halfParams]⟩
private def high : MemristorState halfParams := ⟨3, by norm_num [halfParams],
  by norm_num [halfParams]⟩
private def fullMid : MemristorState fullParams := ⟨2, by norm_num [fullParams],
  by norm_num [fullParams]⟩

example : (memristorStep mid 0) = mid := zero_voltage_identity mid
example : (memristorStep mid 1) = mid := by
  apply subthreshold_stability; norm_num [halfParams]
example : (memristorStep mid (-1)) = mid := by
  apply subthreshold_stability; norm_num [halfParams]
example : (memristorStep mid 2).conductance = 5 / 2 := by
  norm_num [memristorStep, upStep, halfParams, mid]
example : (memristorStep mid (-2)).conductance = 3 / 2 := by
  norm_num [memristorStep, downStep, halfParams, mid]
example : (memristorStep mid 200).conductance = 5 / 2 := by
  norm_num [memristorStep, upStep, halfParams, mid]
example : (memristorStep mid (-200)).conductance = 3 / 2 := by
  norm_num [memristorStep, downStep, halfParams, mid]
example : ¬ (memristorStep mid 2).conductance = mid.conductance := by
  norm_num [memristorStep, upStep, halfParams, mid]
example : ¬ (memristorStep mid (-2)).conductance = mid.conductance := by
  norm_num [memristorStep, downStep, halfParams, mid]
example : (upStep high).conductance = high.conductance := by
  norm_num [upStep, high, halfParams]
example : (downStep low).conductance = low.conductance := by
  norm_num [downStep, low, halfParams]
example : ¬ high.conductance < (upStep high).conductance := by
  norm_num [upStep, high, halfParams]
example : ¬ (downStep low).conductance < low.conductance := by
  norm_num [downStep, low, halfParams]
example : (upStep fullMid).conductance = 3 := by norm_num [upStep, fullMid, fullParams]
example : (downStep fullMid).conductance = 1 := by norm_num [downStep, fullMid, fullParams]
example : (downStep (upStep mid)).conductance = 7 / 4 := by
  norm_num [downStep, upStep, mid, halfParams]
example : (upStep (downStep mid)).conductance = 9 / 4 := by
  norm_num [downStep, upStep, mid, halfParams]
example : (upStep (downStep mid)).conductance - (downStep (upStep mid)).conductance =
    1 / 2 := by norm_num [downStep, upStep, mid, halfParams]
example : current (memristorStep (downStep (upStep mid)) (1 / 2)) (1 / 2) = 7 / 8 ∧
    current (memristorStep (upStep (downStep mid)) (1 / 2)) (1 / 2) = 9 / 8 := by
  norm_num [current, memristorStep, downStep, upStep, mid, halfParams]
example (p : MemristorParameters) (s : MyceliumNodeState p) :
    (memristorStep (memristorStep s p.Vth) (-p.Vth)).conductance <
      (memristorStep (memristorStep s (-p.Vth)) p.Vth).conductance :=
  threshold_history_dependence s
example (p : MemristorParameters) (s : MyceliumNodeState p) (V : ℚ) :
    p.Gmin ≤ (memristorStep s V).conductance ∧ (memristorStep s V).conductance ≤ p.Gmax :=
  conductance_bounds_invariant s V
example : current mid (-3) = -6 := by norm_num [current, mid]
example : power mid (-3) = 18 := by norm_num [power, mid]
example : power mid 0 = 0 := by norm_num [power]
example (p : MemristorParameters) (s : MyceliumNodeState p) (V : ℚ) :
    0 ≤ power s V := power_nonnegative s V
example : spikeGenerator 2 3 = true := by norm_num [spikeGenerator]
example : spikeGenerator 2 2 = false := spike_threshold_inactive 2
example : spikeGenerator 2 1 = false := by norm_num [spikeGenerator]
example : spikeGenerator 2 0 = false := spike_zero_inactive 2 (by norm_num)
example : spikeGenerator 2 (1 + (-1 : ℚ)) = false :=
  spike_noise_margin 2 1 (-1) (by norm_num)
example : spikeGenerator 2 (1 + (1 : ℚ)) = false :=
  spike_noise_margin 2 1 1 (by norm_num)
-- A negative threshold permits a zero-input spike; positivity is a model assumption.
example : spikeGenerator (-1) 0 = true := by norm_num [spikeGenerator]
example : spatialAmplitude 8 (1 / 2) 0 = 8 := by norm_num [spatialAmplitude]
example : spatialAmplitude 8 (1 / 2) 3 = 1 := by norm_num [spatialAmplitude]
example : spatialAmplitude 8 (1 / 2) 4 < spatialAmplitude 8 (1 / 2) 3 := by
  norm_num [spatialAmplitude]
example : spatialAmplitude 8 (1 / 2) 100 ≤ spatialAmplitude 8 (1 / 2) 3 :=
  finite_chain_attenuation 8 (1 / 2) 100 3 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
example (x : ℕ) : spatialAmplitude 0 (1 / 2) x = 0 := by simp [spatialAmplitude]
example : ¬ spatialAmplitude 0 (1 / 2) 1 < spatialAmplitude 0 (1 / 2) 0 := by
  norm_num [spatialAmplitude]
example : spatialAmplitude 1 1 10 = spatialAmplitude 1 1 0 := by norm_num [spatialAmplitude]
example : spatialAmplitude 1 2 1 > spatialAmplitude 1 2 0 := by norm_num [spatialAmplitude]
example : spatialAmplitude (-1) (1 / 2) 1 > spatialAmplitude (-1) (1 / 2) 0 := by
  norm_num [spatialAmplitude]
example : spatialAmplitude 1 0 1 = spatialAmplitude 1 0 2 := by norm_num [spatialAmplitude]
example (x : ℕ) : 0 ≤ spatialAmplitude 8 (1 / 2) x ∧ spatialAmplitude 8 (1 / 2) x ≤ 8 :=
  spatial_attenuation_bound 8 (1 / 2) x (by norm_num) (by norm_num) (by norm_num)
example : FungalMyceliumMemristorSuite := verification_suite

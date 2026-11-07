import Verification.QuantumNoisyBBPSSWCritical
open QuantumNoisyBBPSSW QuantumNoisyBBPSSWConvergence QuantumNoisyBBPSSWCritical
open Filter Topology

example {F : ℝ} (h0 : 0 ≤ F) (h1 : F ≤ 1) :
    Tendsto (noisyOrbit (9 / 10) F) atTop (nhds (1 / 4)) :=
  subcriticalOrbit_tendsto_quarter (by norm_num) nine_tenths_below_critical h0 h1

example : StrictAnti (noisyOrbit (9 / 10) 1) :=
  subcriticalOrbit_strictAnti (by norm_num) nine_tenths_below_critical (by norm_num) le_rfl

example : StrictMono (noisyOrbit (9 / 10) 0) :=
  lowOrbit_strictMono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example (F : ℝ) (n : ℕ) : noisyOrbit 0 F (n + 1) = 1 / 4 := zeroQuality_orbit_succ F n

example (F : ℝ) : Tendsto (noisyOrbit 0 F) atTop (nhds (1 / 4)) := zeroQuality_tendsto F

example (F : ℝ) : ¬ StrictMono (noisyOrbit 0 F) := by
  intro h
  have hs := h (show (1 : ℕ) < 2 by decide)
  have hfirst := zeroQuality_orbit_succ F 0
  have hsecond := zeroQuality_orbit_succ F 1
  norm_num at hfirst hsecond
  rw [hfirst, hsecond] at hs
  exact (lt_irrefl _ hs)

example : (∀ n, noisyOrbit (9 / 10) (1 / 4) n = 1 / 4) :=
  (subcritical_stationary_iff (by norm_num) nine_tenths_below_critical (1 / 4)).mpr rfl

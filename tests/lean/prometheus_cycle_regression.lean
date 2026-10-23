import Verification.PrometheusRSCycleModel
set_option maxRecDepth 20000
open PrometheusRSCycleModel
example (kernel : Instruction → ℕ → ℕ) (finish : ℕ → Status) (a : ℕ) :
    halted (execute kernel finish 2960 (.running program a)) := bounded_execution kernel finish a
example (kernel : Instruction → ℕ → ℕ) (finish : ℕ → Status) (a b : ℕ) :
    ¬ halted (execute kernel finish 2959 (.running program a)) :=
  ((schedule_invariant kernel finish a b).1 2959 (by norm_num)).1
example : serviceSeconds 250000000 = 1184/100000000 := conditional_clock_conversion.1
example : cycles = 2960 := cycles_exact

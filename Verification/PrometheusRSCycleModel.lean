/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.List.Iterate
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Fixed wide-macrocycle control schedule, not a proof of an RS datapath or hardware WCET.
The kernel is an arbitrary total transition: data-dependent muxes cannot change the schedule.
Input framing and CRC are included; repetition voting, serialization and queues are excluded.
-/
set_option maxRecDepth 20000

namespace PrometheusRSCycleModel

inductive Stage where
  | input | syndrome | erasureScan | bm | locator | evaluator | chien | forneyEval
  | correction | verifySyndrome | reencode | compare | crc
  deriving DecidableEq, Repr

abbrev Instruction := Stage × ℕ

def stageProgram (s : Stage) (n : ℕ) : List Instruction := (List.range n).map (s, ·)

def program : List Instruction :=
  stageProgram .input 240 ++ stageProgram .syndrome 240 ++ stageProgram .erasureScan 240 ++
  stageProgram .bm 408 ++ stageProgram .locator 205 ++ stageProgram .evaluator 204 ++
  stageProgram .chien 205 ++ stageProgram .forneyEval 205 ++ stageProgram .correction 240 ++
  stageProgram .verifySyndrome 240 ++ stageProgram .reencode 36 ++
  stageProgram .compare 240 ++ stageProgram .crc 256

def cycles : ℕ := program.length + 1

theorem cycles_exact : cycles = 2960 := by
  norm_num [cycles, program, stageProgram]

inductive Status where
  | success | uncorrectableFailure
  deriving DecidableEq, Repr

inductive State (α : Type*) where
  | running (pending : List Instruction) (data : α)
  | done (status : Status)

variable {α : Type*}

def step (kernel : Instruction → α → α) (finish : α → Status) : State α → State α
  | .running [] a => .done (finish a)
  | .running (i :: rest) a => .running rest (kernel i a)
  | .done s => .done s

def execute (kernel : Instruction → α → α) (finish : α → Status) : ℕ → State α → State α
  | 0, state => state
  | n + 1, state => execute kernel finish n (step kernel finish state)

def halted : State α → Prop
  | .done _ => True
  | .running _ _ => False

theorem execution_result (kernel : Instruction → α → α) (finish : α → Status)
    (instructions : List Instruction) (a : α) :
    execute kernel finish (instructions.length + 1) (.running instructions a) =
      .done (finish (instructions.foldl (fun x i => kernel i x) a)) := by
  induction instructions generalizing a with
  | nil => rfl
  | cons i rest ih =>
    simpa only [List.length_cons, execute, step, List.foldl_cons] using ih (kernel i a)

theorem no_early_halt (kernel : Instruction → α → α) (finish : α → Status)
    (instructions : List Instruction) (a : α) (n : ℕ) (hn : n ≤ instructions.length) :
    ¬ halted (execute kernel finish n (.running instructions a)) := by
  induction instructions generalizing a n with
  | nil =>
    have : n = 0 := by simpa using hn
    subst n
    simp [execute, halted]
  | cons i rest ih =>
    cases n with
    | zero => simp [execute, halted]
    | succ n =>
      apply ih (kernel i a) n
      simpa using hn

theorem bounded_execution (kernel : Instruction → α → α) (finish : α → Status) (a : α) :
    halted (execute kernel finish 2960 (.running program a)) := by
  rw [← cycles_exact]
  unfold cycles
  rw [execution_result]
  trivial

/-- Exact termination time is independent of error counts, data and the total datapath kernel. -/
theorem schedule_invariant (kernel : Instruction → α → α) (finish : α → Status) (a b : α) :
    (∀ n < 2960, ¬ halted (execute kernel finish n (.running program a)) ∧
      ¬ halted (execute kernel finish n (.running program b))) ∧
    halted (execute kernel finish 2960 (.running program a)) ∧
    halted (execute kernel finish 2960 (.running program b)) := by
  constructor
  · intro n hn
    have hlen : n ≤ program.length := by have := cycles_exact; unfold cycles at this; omega
    constructor
    · exact no_early_halt kernel finish program a n hlen
    · exact no_early_halt kernel finish program b n hlen
  · constructor
    · exact bounded_execution kernel finish a
    · exact bounded_execution kernel finish b

/-- Seconds per complete frame, conditional on an unstalled clock at the stated frequency. -/
def serviceSeconds (frequencyHz : ℚ) : ℚ := (cycles : ℚ) / frequencyHz

theorem conditional_clock_conversion :
    serviceSeconds 250000000 = 1184 / 100000000 ∧
      serviceSeconds 500000000 = 592 / 100000000 := by
  norm_num [serviceSeconds, cycles_exact]

structure PrometheusRSCycleModelSuite : Prop where
  termination : ∀ (kernel : Instruction → ℕ → ℕ) (finish : ℕ → Status) (a : ℕ),
    halted (execute kernel finish 2960 (.running program a))
  count : cycles = 2960
  duration : serviceSeconds 250000000 = 1184 / 100000000

theorem verification_suite : PrometheusRSCycleModelSuite :=
  ⟨bounded_execution, cycles_exact, conditional_clock_conversion.1⟩

end PrometheusRSCycleModel

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Deterministic single-server decoder queue and conditional route budget

All times are real numbers expressed in one consistent unit. Packets are served
in index order, without preemption or dropping, by one server. The algebraic
identities hold for arbitrary input sequences; physical chronological arrivals
and nonnegative service are explicit predicates, not measured facts. There is
no finite-buffer, scheduler, stochastic stability, WCET or CPU refinement claim.
An initially empty queue means the initial server availability is no later than
the first arrival. The exact serialization examples use milliseconds.
-/
namespace PrometheusDecoderQueue
noncomputable section

/-- Arrival and service sequences; validity is supplied separately. -/
structure QueueInput where
  arrival : ℕ → ℝ
  service : ℕ → ℝ
  initialAvailable : ℝ

/-- Chronological FIFO input with nonnegative service and an initially idle server. -/
def QueueInput.Valid (q : QueueInput) : Prop :=
  Monotone q.arrival ∧ (∀ i, 0 ≤ q.service i) ∧ q.initialAvailable ≤ q.arrival 0

/-- Server availability just before packet i is selected in FIFO index order. -/
def ready (q : QueueInput) : ℕ → ℝ
  | 0 => q.initialAvailable
  | i + 1 => max (q.arrival i) (ready q i) + q.service i

def start (q : QueueInput) (i : ℕ) : ℝ := max (q.arrival i) (ready q i)
def finish (q : QueueInput) (i : ℕ) : ℝ := start q i + q.service i
def waiting (q : QueueInput) (i : ℕ) : ℝ := start q i - q.arrival i
def sojourn (q : QueueInput) (i : ℕ) : ℝ := finish q i - q.arrival i

@[simp] theorem ready_zero (q : QueueInput) : ready q 0 = q.initialAvailable := rfl
@[simp] theorem ready_succ (q : QueueInput) (i : ℕ) : ready q (i + 1) = finish q i := rfl

theorem arrival_le_start (q : QueueInput) (i : ℕ) : q.arrival i ≤ start q i :=
  le_max_left _ _

theorem waiting_nonnegative (q : QueueInput) (i : ℕ) : 0 ≤ waiting q i :=
  sub_nonneg.mpr (arrival_le_start q i)

theorem sojourn_eq_waiting_add_service (q : QueueInput) (i : ℕ) :
    sojourn q i = waiting q i + q.service i := by
  unfold sojourn finish waiting
  ring

theorem sojourn_nonnegative (q : QueueInput) (i : ℕ) (hs : 0 ≤ q.service i) :
    0 ≤ sojourn q i := by
  rw [sojourn_eq_waiting_add_service]
  exact add_nonneg (waiting_nonnegative q i) hs

theorem finish_le_next_start (q : QueueInput) (i : ℕ) : finish q i ≤ start q (i + 1) := by
  change finish q i ≤ max (q.arrival (i + 1)) (ready q (i + 1))
  rw [ready_succ]
  exact le_max_right _ _

private theorem max_sub_left (a b : ℝ) : max a b - a = max 0 (b - a) := by
  by_cases h : b ≤ a
  · rw [max_eq_left h, max_eq_left (sub_nonpos.mpr h)]
    ring
  · have h' : a ≤ b := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h', max_eq_right (sub_nonneg.mpr h')]

theorem waiting_eq_max (q : QueueInput) (i : ℕ) :
    waiting q i = max 0 (ready q i - q.arrival i) :=
  max_sub_left _ _

theorem waiting_zero_of_initial_idle (q : QueueInput)
    (h : q.initialAvailable ≤ q.arrival 0) : waiting q 0 = 0 := by
  rw [waiting_eq_max, ready_zero, max_eq_left (sub_nonpos.mpr h)]

theorem lindley_recurrence (q : QueueInput) (i : ℕ) :
    waiting q (i + 1) =
      max 0 (waiting q i + q.service i - (q.arrival (i + 1) - q.arrival i)) := by
  rw [waiting_eq_max q (i + 1), ready_succ]
  congr 1
  unfold finish waiting
  ring

/-- Exact periodic arrivals; a service bound alone does not imply this premise. -/
def PeriodicArrivals (q : QueueInput) (period : ℝ) : Prop :=
  ∀ i, q.arrival (i + 1) - q.arrival i = period

theorem periodic_zero_waiting (q : QueueInput) (period : ℝ)
    (_hperiod : 0 < period) (hperiodic : PeriodicArrivals q period)
    (hidle : q.initialAvailable ≤ q.arrival 0)
    (hservice : ∀ i, 0 ≤ q.service i ∧ q.service i ≤ period) :
    ∀ i, waiting q i = 0 := by
  intro i
  induction i with
  | zero => exact waiting_zero_of_initial_idle q hidle
  | succ i ih =>
      rw [lindley_recurrence, hperiodic i, ih, zero_add]
      exact max_eq_left (sub_nonpos.mpr (hservice i).2)

/-- A concrete periodic FIFO input, with server initially available at the first arrival. -/
def periodicQueue (epoch period serviceTime : ℝ) : QueueInput where
  arrival i := epoch + (i : ℝ) * period
  service _ := serviceTime
  initialAvailable := epoch

theorem periodicQueue_periodic (epoch period serviceTime : ℝ) :
    PeriodicArrivals (periodicQueue epoch period serviceTime) period := by
  intro i
  simp only [periodicQueue, Nat.cast_add, Nat.cast_one]
  ring

theorem periodicQueue_valid (epoch period serviceTime : ℝ)
    (hperiod : 0 ≤ period) (hservice : 0 ≤ serviceTime) :
    (periodicQueue epoch period serviceTime).Valid := by
  refine ⟨?_, fun _ => hservice, ?_⟩
  · intro i j hij
    change epoch + (i : ℝ) * period ≤ epoch + (j : ℝ) * period
    have h : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith [mul_le_mul_of_nonneg_right h hperiod]
  · simp [periodicQueue]

theorem constant_overload_waiting (q : QueueInput) (period serviceTime : ℝ)
    (hperiodic : PeriodicArrivals q period)
    (hidle : q.initialAvailable ≤ q.arrival 0)
    (hservice : ∀ i, q.service i = serviceTime) (hoverload : period ≤ serviceTime) :
    ∀ i, waiting q i = (i : ℝ) * (serviceTime - period) := by
  intro i
  induction i with
  | zero => simpa using waiting_zero_of_initial_idle q hidle
  | succ i ih =>
      rw [lindley_recurrence, hperiodic i, hservice i, ih]
      have hn : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
      have hg : 0 ≤ serviceTime - period := sub_nonneg.mpr hoverload
      rw [max_eq_right (by nlinarith [mul_nonneg hn hg])]
      push_cast
      ring

theorem periodic_overload_waiting (epoch period serviceTime : ℝ)
    (hoverload : period ≤ serviceTime) (i : ℕ) :
    waiting (periodicQueue epoch period serviceTime) i =
      (i : ℝ) * (serviceTime - period) := by
  apply constant_overload_waiting _ period serviceTime
    (periodicQueue_periodic epoch period serviceTime)
  · simp [periodicQueue]
  · intro j; rfl
  · exact hoverload

theorem periodic_overload_growth (epoch period serviceTime : ℝ)
    (hoverload : period < serviceTime) (i : ℕ) :
    waiting (periodicQueue epoch period serviceTime) i <
      waiting (periodicQueue epoch period serviceTime) (i + 1) := by
  rw [periodic_overload_waiting _ _ _ (le_of_lt hoverload),
      periodic_overload_waiting _ _ _ (le_of_lt hoverload)]
  push_cast
  nlinarith

/-- Infinite index extension with no dropped packets; not a finite-buffer guarantee. -/
theorem periodic_overload_unbounded (epoch period serviceTime : ℝ)
    (hoverload : period < serviceTime) (bound : ℝ) :
    ∃ i, bound < waiting (periodicQueue epoch period serviceTime) i := by
  obtain ⟨i, hi⟩ := exists_nat_gt (bound / (serviceTime - period))
  refine ⟨i, ?_⟩
  rw [periodic_overload_waiting _ _ _ (le_of_lt hoverload)]
  exact (div_lt_iff₀ (sub_pos.mpr hoverload)).mp hi

/-- Positive-period specialization provides a valid chronological queue as well
as the unbounded waiting conclusion. The more general formula above is algebraic. -/
theorem positive_period_overload (epoch period serviceTime : ℝ)
    (hperiod : 0 < period) (hoverload : period < serviceTime) :
    (periodicQueue epoch period serviceTime).Valid ∧
      ∀ bound, ∃ i, bound < waiting (periodicQueue epoch period serviceTime) i := by
  exact ⟨periodicQueue_valid epoch period serviceTime (le_of_lt hperiod)
    (le_of_lt (lt_trans hperiod hoverload)),
    periodic_overload_unbounded epoch period serviceTime hoverload⟩

/-- Serialization only; acquisition, encoding and transport are separate terms. -/
def serialization (slots : ℕ) (slotTime : ℝ) : ℝ := (slots : ℝ) * slotTime

def tenNanosecondsMs : ℝ := 1 / 100000
def frameSerializationMs : ℝ := serialization 9600 tenNanosecondsMs

theorem serialization_nonnegative (slots : ℕ) (slotTime : ℝ) (h : 0 ≤ slotTime) :
    0 ≤ serialization slots slotTime := mul_nonneg (Nat.cast_nonneg slots) h

theorem frame_serialization_exact : frameSerializationMs = 96 / 1000 := by
  norm_num [frameSerializationMs, serialization, tenNanosecondsMs]

/-- Counterexample in milliseconds: every service is at most 1ms, yet queueing grows.
Hence even a pointwise 1ms bound (stronger than a median bound) is insufficient
for a stream arriving every 96us. No empirical timing is used as a premise. -/
theorem one_ms_service_counterexample :
    (∀ i, (periodicQueue 0 frameSerializationMs 1).service i ≤ 1) ∧
    waiting (periodicQueue 0 frameSerializationMs 1) 1 = 904 / 1000 ∧
    waiting (periodicQueue 0 frameSerializationMs 1) 2 = 1808 / 1000 := by
  rw [frame_serialization_exact]
  refine ⟨fun _ => le_refl _, ?_, ?_⟩
  · rw [periodic_overload_waiting _ _ _ (by norm_num)]
    norm_num
  · rw [periodic_overload_waiting _ _ _ (by norm_num)]
    norm_num

/-- All route components have the same unit. `extra` includes any unmodeled costs
only when independently supplied; zero extra is an explicit assumption. -/
structure RouteBudget where
  encode : ℝ
  serialize : ℝ
  propagate : ℝ
  wait : ℝ
  service : ℝ
  extra : ℝ

def RouteBudget.Nonnegative (b : RouteBudget) : Prop :=
  0 ≤ b.encode ∧ 0 ≤ b.serialize ∧ 0 ≤ b.propagate ∧
    0 ≤ b.wait ∧ 0 ≤ b.service ∧ 0 ≤ b.extra

def RouteBudget.total (b : RouteBudget) : ℝ :=
  b.encode + b.serialize + b.propagate + b.wait + b.service + b.extra

def RouteBudget.BoundedBy (b cap : RouteBudget) : Prop :=
  b.encode ≤ cap.encode ∧ b.serialize ≤ cap.serialize ∧ b.propagate ≤ cap.propagate ∧
    b.wait ≤ cap.wait ∧ b.service ≤ cap.service ∧ b.extra ≤ cap.extra

theorem route_total_nonnegative (b : RouteBudget) (h : b.Nonnegative) : 0 ≤ b.total := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  unfold RouteBudget.total
  linarith

theorem route_total_upper_bound (b cap : RouteBudget)
    (_h : b.Nonnegative) (hbound : b.BoundedBy cap) : b.total ≤ cap.total := by
  rcases hbound with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  unfold RouteBudget.total
  linarith

theorem route_saving_lower_bound (b cap : RouteBudget) (reference : ℝ)
    (h : b.Nonnegative) (hbound : b.BoundedBy cap) :
    reference - cap.total ≤ reference - b.total := by
  linarith [route_total_upper_bound b cap h hbound]

/-- Attach the actual queue waiting/service and exact serialization terms. -/
def packetBudget (q : QueueInput) (i slots : ℕ)
    (slotTime encode propagate extra : ℝ) : RouteBudget where
  encode := encode
  serialize := serialization slots slotTime
  propagate := propagate
  wait := waiting q i
  service := q.service i
  extra := extra

theorem packet_budget_nonnegative (q : QueueInput) (i slots : ℕ)
    (slotTime encode propagate extra : ℝ) (hslot : 0 ≤ slotTime)
    (hencode : 0 ≤ encode) (hpropagate : 0 ≤ propagate)
    (hservice : 0 ≤ q.service i) (hextra : 0 ≤ extra) :
    (packetBudget q i slots slotTime encode propagate extra).Nonnegative :=
  ⟨hencode, serialization_nonnegative slots slotTime hslot, hpropagate,
    waiting_nonnegative q i, hservice, hextra⟩

theorem packet_total_eq (q : QueueInput) (i slots : ℕ)
    (slotTime encode propagate extra : ℝ) :
    (packetBudget q i slots slotTime encode propagate extra).total =
      encode + serialization slots slotTime + propagate + sojourn q i + extra := by
  rw [sojourn_eq_waiting_add_service]
  unfold RouteBudget.total packetBudget
  ring

/-- Example upper bounds in milliseconds; these are assumptions, not timings. -/
def exampleCapMs : RouteBudget := ⟨1, 96 / 1000, 40410 / 1000, 0, 1, 0⟩

theorem example_cap_total : exampleCapMs.total = 42506 / 1000 := by
  norm_num [exampleCapMs, RouteBudget.total]

theorem conditional_example_saving (b : RouteBudget) (h : b.Nonnegative)
    (hbound : b.BoundedBy exampleCapMs) :
    35415 / 1000 ≤ (77921 / 1000 : ℝ) - b.total := by
  have hs := route_saving_lower_bound b exampleCapMs (77921 / 1000) h hbound
  rw [example_cap_total] at hs
  linarith

structure PrometheusDecoderQueueSuite : Prop where
  nonnegative : ∀ q i, 0 ≤ waiting q i
  sojourn_identity : ∀ q i, sojourn q i = waiting q i + q.service i
  lindley : ∀ q i, waiting q (i + 1) =
    max 0 (waiting q i + q.service i - (q.arrival (i + 1) - q.arrival i))
  periodic_idle : ∀ q A, 0 < A → PeriodicArrivals q A →
    q.initialAvailable ≤ q.arrival 0 → (∀ i, 0 ≤ q.service i ∧ q.service i ≤ A) →
    ∀ i, waiting q i = 0
  overload : ∀ epoch A s, A < s → ∀ bound,
    ∃ i, bound < waiting (periodicQueue epoch A s) i
  physical_overload : ∀ epoch A s, 0 < A → A < s →
    (periodicQueue epoch A s).Valid ∧ ∀ bound,
      ∃ i, bound < waiting (periodicQueue epoch A s) i
  one_ms_backlog : waiting (periodicQueue 0 frameSerializationMs 1) 1 = 904 / 1000
  serialize_exact : frameSerializationMs = 96 / 1000
  budget_bound : ∀ (b cap : RouteBudget), b.Nonnegative → b.BoundedBy cap → b.total ≤ cap.total
  saving : ∀ (b : RouteBudget), b.Nonnegative → b.BoundedBy exampleCapMs →
    35415 / 1000 ≤ (77921 / 1000 : ℝ) - b.total

theorem verification_suite : PrometheusDecoderQueueSuite :=
  ⟨waiting_nonnegative, sojourn_eq_waiting_add_service, lindley_recurrence,
    periodic_zero_waiting, periodic_overload_unbounded, positive_period_overload,
    one_ms_service_counterexample.2.1, frame_serialization_exact,
    route_total_upper_bound, conditional_example_saving⟩

end
end PrometheusDecoderQueue

import Verification.PrometheusDecoderQueue

open PrometheusDecoderQueue
noncomputable section

-- API applications; arbitrary sequences do not implicitly satisfy QueueInput.Valid.
example (q : QueueInput) (i : ℕ) : 0 ≤ waiting q i := waiting_nonnegative q i
example (q : QueueInput) (i : ℕ) : sojourn q i = waiting q i + q.service i :=
  sojourn_eq_waiting_add_service q i
example (q : QueueInput) (i : ℕ) : finish q i ≤ start q (i + 1) :=
  finish_le_next_start q i
example (q : QueueInput) (i : ℕ) : waiting q (i + 1) =
    max 0 (waiting q i + q.service i - (q.arrival (i + 1) - q.arrival i)) :=
  lindley_recurrence q i
example (q : QueueInput) (h : q.Valid) : waiting q 0 = 0 :=
  waiting_zero_of_initial_idle q h.2.2
example (q : QueueInput) (h : q.Valid) (i : ℕ) : 0 ≤ sojourn q i :=
  sojourn_nonnegative q i (h.2.1 i)
example (epoch : ℝ) : (periodicQueue epoch 1 (1 / 2)).Valid :=
  periodicQueue_valid _ _ _ (by norm_num) (by norm_num)

-- Independent rational expected values, zero duration and exact boundary load.
example : waiting (periodicQueue 7 1 (1 / 2)) 0 = 0 := by
  norm_num [waiting, start, ready, periodicQueue]
example : finish (periodicQueue 7 1 (1 / 2)) 0 = 15 / 2 := by
  norm_num [finish, start, ready, periodicQueue]
example : sojourn (periodicQueue 7 1 (1 / 2)) 2 = 1 / 2 := by
  norm_num [sojourn, finish, start, ready, periodicQueue]
example (i : ℕ) : waiting (periodicQueue 7 1 (1 / 2)) i = 0 := by
  apply periodic_zero_waiting _ 1 (by norm_num) (periodicQueue_periodic _ _ _)
  · norm_num [periodicQueue]
  · intro j; norm_num [periodicQueue]
example (i : ℕ) : waiting (periodicQueue 0 1 1) i = 0 := by
  rw [periodic_overload_waiting _ _ _ (by norm_num)]
  simp
example : sojourn (periodicQueue 0 1 0) 5 = 0 := by
  norm_num [sojourn, finish, start, ready, periodicQueue]
example : waiting (periodicQueue 0 (3 / 2) 2) 4 = 2 := by
  rw [periodic_overload_waiting _ _ _ (by norm_num)]
  norm_num
example : waiting (periodicQueue 0 (3 / 2) 2) 5 = 5 / 2 := by
  rw [periodic_overload_waiting _ _ _ (by norm_num)]
  norm_num
example : waiting (periodicQueue 0 (3 / 2) 2) 4 < waiting (periodicQueue 0 (3 / 2) 2) 5 :=
  periodic_overload_growth _ _ _ (by norm_num) _
example (bound : ℝ) : ∃ i, bound < waiting (periodicQueue 0 (3 / 2) 2) i :=
  (positive_period_overload 0 (3 / 2) 2 (by norm_num) (by norm_num)).2 bound

-- Initial-idle and arrival-spacing premises cannot be discarded.
def busy : QueueInput := ⟨fun i => (i : ℝ), fun _ => 1 / 2, 3⟩
example : waiting busy 0 = 3 := by norm_num [waiting, start, ready, busy]
example : waiting busy 1 = 5 / 2 := by norm_num [waiting, start, ready, busy]
example : waiting busy 6 = 0 := by norm_num [waiting, start, ready, busy]
example : ¬busy.Valid := by
  intro h
  have h' := h.2.2
  norm_num [busy] at h'
def simultaneous : QueueInput := ⟨fun _ => 0, fun _ => 1, 0⟩
example : simultaneous.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij; exact le_refl _
  · intro i; norm_num [simultaneous]
  · norm_num [simultaneous]
example : waiting simultaneous 1 = 1 := by
  norm_num [waiting, start, ready, simultaneous]
example : (∀ i, simultaneous.service i ≤ 1) ∧ waiting simultaneous 1 ≠ 0 := by
  constructor
  · intro i; exact le_refl _
  · norm_num [waiting, start, ready, simultaneous]
example : sojourn (periodicQueue 0 1 (-1)) 0 = -1 := by
  norm_num [sojourn, finish, start, ready, periodicQueue]
example : ¬(periodicQueue 0 1 (-1)).Valid := by
  intro h
  have h' := h.2.1 0
  norm_num [periodicQueue] at h'

-- A long first service followed by short ones drains: use service i, not i+1.
def transient : QueueInput := ⟨fun i => (i : ℝ), fun i => if i = 0 then 2 else 0, 0⟩
example : waiting transient 1 = 1 := by norm_num [waiting, start, ready, transient]
example : waiting transient 2 = 0 := by norm_num [waiting, start, ready, transient]

-- Exact unit conversion and counterexample stronger than a median ≤1ms claim.
example : serialization 0 tenNanosecondsMs = 0 := by simp [serialization]
example : serialization 9600 tenNanosecondsMs = 96 / 1000 := frame_serialization_exact
example : serialization 10000 tenNanosecondsMs = 1 / 10 := by
  norm_num [serialization, tenNanosecondsMs]
example : waiting (periodicQueue 0 frameSerializationMs 1) 1 = 904 / 1000 :=
  one_ms_service_counterexample.2.1
example : waiting (periodicQueue 0 frameSerializationMs 1) 2 = 1808 / 1000 :=
  one_ms_service_counterexample.2.2
example : 0 < waiting (periodicQueue 0 frameSerializationMs 1) 1 := by
  rw [one_ms_service_counterexample.2.1]
  norm_num

-- Complete conditional route accounting; extra/wait bounds are independent inputs.
example : exampleCapMs.Nonnegative := by
  norm_num [RouteBudget.Nonnegative, exampleCapMs]
example : exampleCapMs.total = 42506 / 1000 := example_cap_total
example : (77921 / 1000 : ℝ) - exampleCapMs.total = 35415 / 1000 := by
  rw [example_cap_total]
  norm_num
example (b : RouteBudget) (h : b.Nonnegative) (hb : b.BoundedBy exampleCapMs) :
    b.total ≤ 42506 / 1000 := by
  simpa [example_cap_total] using route_total_upper_bound b exampleCapMs h hb
example (b : RouteBudget) (h : b.Nonnegative) (hb : b.BoundedBy exampleCapMs) :
    35415 / 1000 ≤ (77921 / 1000 : ℝ) - b.total := conditional_example_saving b h hb
example : (packetBudget (periodicQueue 0 1 (1 / 2)) 2 9600
    tenNanosecondsMs 1 (40410 / 1000) 0).Nonnegative := by
  apply packet_budget_nonnegative <;> norm_num [tenNanosecondsMs, periodicQueue]
example (q : QueueInput) (i n : ℕ) (slot enc prop extra : ℝ) :
    (packetBudget q i n slot enc prop extra).total =
      enc + serialization n slot + prop + sojourn q i + extra :=
  packet_total_eq q i n slot enc prop extra
example : (77921 / 1000 : ℝ) <
    (RouteBudget.mk 0 (96 / 1000) (40410 / 1000) 0 1 100).total := by
  norm_num [RouteBudget.total]
example : (RouteBudget.mk 0 (96 / 1000) (40410 / 1000) 0 1 100).Nonnegative := by
  norm_num [RouteBudget.Nonnegative]
example : ¬(RouteBudget.mk 0 (96 / 1000) (40410 / 1000) 0 1 100).BoundedBy exampleCapMs := by
  norm_num [RouteBudget.BoundedBy, exampleCapMs]

import Verification.PrometheusPipelinedQueue
import Mathlib.Data.Finset.Range

open PrometheusPipelinedQueue PrometheusDecoderQueue

-- The lane recurrence uses the inherited FIFO queue, with unchanged full service time.
example (q : QueueInput) (i : ℕ) : ready q (i + 1) = finish q i := ready_succ q i
example (P : ℕ) (l : Fin P) (e dt S : ℝ) (i : ℕ) :
    (cyclicLane P l e dt S).arrival i = e + ((P * i + l : ℕ) : ℝ) * dt :=
  cyclic_arrival P l e dt S i
example (P : ℕ) (l : Fin P) (e dt S : ℝ) (i : ℕ) :
    (cyclicLane P l e dt S).service i = S := rfl
example : (cyclicLane 20 ⟨3, by norm_num⟩ 0 (1 / 5) 4).arrival 2 = 43 / 5 := by
  rw [cyclic_arrival]
  norm_num
example (l : Fin 20) :
    LaneEnvelope (cyclicLane 20 l 0 (1 / 5) 4) ((l : ℕ) * (1 / 5)) 4 0 4 := by
  convert cyclic_envelope 20 (by norm_num) l 0 (1 / 5) 4
    (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num
example (l : Fin 20) (i : ℕ) : waiting (cyclicLane 20 l 0 (1 / 5) 4) i = 0 :=
  (twenty_lane_example l i).1
example (l : Fin 20) (i : ℕ) :
    routeLatency (cyclicLane 20 l 0 (1 / 5) 4) i (1 / 5) (40411 / 1000) < 45 :=
  (twenty_lane_example l i).2
example (q : QueueInput) (e A J S : ℝ) (h : LaneEnvelope q e A J S) : q.Valid := lane_valid h
example (q : QueueInput) (e A J S : ℝ) (h : LaneEnvelope q e A J S) (i : ℕ) :
    start q i ≤ e + i * A + J := start_upper h i
example (q : QueueInput) (e A J S : ℝ) (h : LaneEnvelope q e A J S) (i : ℕ) :
    waiting q i ≤ J := waiting_upper h i
example (q : QueueInput) (e A J S : ℝ) (h : LaneEnvelope q e A J S) (i : ℕ) :
    sojourn q i ≤ J + S := sojourn_upper h i
example (q : QueueInput) (e A J S : ℝ) (h : LaneEnvelope q e A J S)
    (b horizon : ℕ) (t : ℝ) (hb : J ≤ b * A) : (waitingSet q horizon t).card ≤ b :=
  waiting_card_bound h b horizon t hb
example (l : Fin 20) (horizon : ℕ) (t : ℝ) :
    (waitingSet (cyclicLane 20 l 0 (1 / 5) 4) horizon t).card = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply waiting_card_bound (cyclic_envelope 20 (by norm_num) l 0 (1 / 5) 4
    (by norm_num) (by norm_num) (by norm_num)) 0 horizon t
  norm_num
example (lanes : Fin 20 → QueueInput) (epoch : Fin 20 → ℝ) (horizon : ℕ) (t : ℝ)
    (h : ∀ l, LaneEnvelope (lanes l) (epoch l) 4 (1 / 5) 4) :
    bufferOverflow lanes 20 horizon t = false := by
  exact finite_buffer_no_overflow (by norm_num) lanes epoch 4 (1 / 5) 4
    1 20 horizon t h (by norm_num) (by norm_num)

-- Capacity is waiting-only: a simultaneous burst of three leaves two waiting.
example : (waitingSet (periodicQueue 0 0 1) 3 0).card = 2 := by
  norm_num [waitingSet, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton, start, ready, periodicQueue]
example : bufferOverflow (fun _ : Fin 1 => periodicQueue 0 0 1) 1 3 0 = true := by
  norm_num [bufferOverflow, poolWaiting, waitingSet, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton, start, ready,
    periodicQueue]
example : (waitingSet (periodicQueue 0 0 1) 1 0).card = 0 := by
  norm_num [waitingSet, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton, start, ready, periodicQueue]
example : (waitingSet (periodicQueue 0 0 1) 3 1).card = 1 := by
  norm_num [waitingSet, Finset.range_add_one, Finset.filter_insert, Finset.filter_singleton, start, ready, periodicQueue]

-- Throughput and individual packet latency are separate.
example : (64 : ℝ) * (96 / 1000) < 6234 / 1000 ∧
    6234 / 1000 ≤ (65 : ℝ) * (96 / 1000) := throughput_lane_count_example
example (l : Fin 65) (i : ℕ) :
    waiting (cyclicLane 65 l 0 (96 / 1000) (6234 / 1000)) i = 0 := by
  apply cyclic_zero_waiting <;> norm_num
example (l : Fin 65) (i : ℕ) :
    45 < packetLatency (cyclicLane 65 l 0 (96 / 1000) (6234 / 1000)) i (96 / 1000) := by
  apply six_ms_service_obstruction <;> norm_num [cyclicLane, periodicQueue]
example (q : QueueInput) (e A J S : ℝ) (h : LaneEnvelope q e A J S) (i : ℕ)
    (hJ : J ≤ 1 / 5) (hS : S ≤ 4) : routeLatency q i (1 / 5) (40411 / 1000) < 45 :=
  conditional_45ms h i _ _ (by norm_num) hJ hS (by norm_num)
example (q : QueueInput) (e A J S : ℝ) (h : LaneEnvelope q e A J S) (i : ℕ)
    (hJ : J ≤ 1 / 5) (hS : S ≤ 4) :
    routeLatency q i (1 / 5) (40411 / 1000) < 77921 / 1000 :=
  conditional_fiber_advantage h i _ _ (by norm_num) hJ hS (by norm_num)
example : (40411 / 1000 : ℝ) + 1 / 5 + 1 / 5 + 4 = 44811 / 1000 := by norm_num

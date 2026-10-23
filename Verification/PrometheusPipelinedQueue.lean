/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PrometheusDecoderQueue
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
# Cyclic parallel decoder lanes with a finite waiting-buffer certificate

Each lane uses the existing nonpreemptive FIFO recurrence. A bounded-jitter arrival
envelope and a service envelope imply actual start/wait/sojourn bounds. The buffer
counts waiting packets only, excluding packets in service, at arbitrary real times
in every finite prefix. Its non-overflow certificate establishes capacity of this
explicit no-drop schedule; a dropped-job implementation is not refined here.
Static cyclic routing is not a shared work-conserving dispatch policy. Parallelism
changes lane arrival spacing; it never divides one packet's service latency.
-/
namespace PrometheusPipelinedQueue
noncomputable section
open PrometheusDecoderQueue
open scoped BigOperators

/-- All times use one unit. Chronological arrivals are an independent premise. -/
structure LaneEnvelope (q : QueueInput) (epoch period jitter serviceCap : ℝ) : Prop where
  period_pos : 0 < period
  jitter_nonnegative : 0 ≤ jitter
  chronological : Monotone q.arrival
  arrival_lower : ∀ i : ℕ, epoch + (i : ℝ) * period ≤ q.arrival i
  arrival_upper : ∀ i : ℕ, q.arrival i ≤ epoch + (i : ℝ) * period + jitter
  service_nonnegative : ∀ i, 0 ≤ q.service i
  service_upper : ∀ i, q.service i ≤ serviceCap
  service_fits : serviceCap ≤ period
  initially_idle : q.initialAvailable ≤ q.arrival 0

theorem lane_valid {q : QueueInput} {e A J S : ℝ} (h : LaneEnvelope q e A J S) :
    q.Valid := ⟨h.chronological, h.service_nonnegative, h.initially_idle⟩

/-- Derived from the ready recurrence, not supplied as a queue-bound hypothesis. -/
theorem start_upper {q : QueueInput} {e A J S : ℝ} (h : LaneEnvelope q e A J S) :
    ∀ i, start q i ≤ e + (i : ℝ) * A + J := by
  intro i
  induction i with
  | zero =>
      change max (q.arrival 0) q.initialAvailable ≤ _
      exact max_le (h.arrival_upper 0) (h.initially_idle.trans (h.arrival_upper 0))
  | succ i ih =>
      change max (q.arrival (i + 1)) (ready q (i + 1)) ≤ _
      rw [ready_succ]
      apply max_le (h.arrival_upper (i + 1))
      have hs := h.service_upper i
      have hf := h.service_fits
      unfold finish
      push_cast
      linarith

theorem waiting_upper {q : QueueInput} {e A J S : ℝ} (h : LaneEnvelope q e A J S)
    (i : ℕ) : waiting q i ≤ J := by
  have hu := start_upper h i
  have hl := h.arrival_lower i
  unfold waiting
  linarith

theorem sojourn_upper {q : QueueInput} {e A J S : ℝ} (h : LaneEnvelope q e A J S)
    (i : ℕ) : sojourn q i ≤ J + S := by
  rw [sojourn_eq_waiting_add_service]
  exact add_le_add (waiting_upper h i) (h.service_upper i)

/-- A packet is waiting at t iff it has arrived but has not started service. -/
def waitingSet (q : QueueInput) (horizon : ℕ) (t : ℝ) : Finset ℕ :=
  (Finset.range horizon).filter fun i => q.arrival i ≤ t ∧ t < start q i

/-- At most b waiting packets per lane, including simultaneous arrivals. -/
theorem waiting_card_bound {q : QueueInput} {e A J S : ℝ}
    (h : LaneEnvelope q e A J S) (b horizon : ℕ) (t : ℝ) (hburst : J ≤ (b : ℝ) * A) :
    (waitingSet q horizon t).card ≤ b := by
  classical
  let w := waitingSet q horizon t
  by_cases hw : w.Nonempty
  · let m := w.min' hw
    have hm : m ∈ w := Finset.min'_mem w hw
    have hmwait : t < start q m := (Finset.mem_filter.mp hm).2.2
    have hsub : w ⊆ Finset.Ico m (m + b) := by
      intro j hj
      have hlo : m ≤ j := Finset.min'_le w j hj
      have hjarr : q.arrival j ≤ t := (Finset.mem_filter.mp hj).2.1
      have hmstart := start_upper h m
      have hjlower := h.arrival_lower j
      have hprod : (j : ℝ) * A < ((m : ℝ) + b) * A := by nlinarith
      have hreal : (j : ℝ) < (m : ℝ) + b :=
        (mul_lt_mul_iff_left₀ h.period_pos).mp hprod
      have hnat : j < m + b := by exact_mod_cast hreal
      exact Finset.mem_Ico.mpr ⟨hlo, hnat⟩
    have hc := Finset.card_le_card hsub
    simpa using hc
  · have he : w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hw
    simp [w, he] at *

/-- Independent FIFO lanes. P=0 is excluded in physical pool contracts. -/
def poolWaiting {P : ℕ} (lanes : Fin P → QueueInput) (horizon : ℕ) (t : ℝ) : ℕ :=
  ∑ l, (waitingSet (lanes l) horizon t).card

def bufferOverflow {P : ℕ} (lanes : Fin P → QueueInput)
    (buffer horizon : ℕ) (t : ℝ) : Bool := decide (buffer < poolWaiting lanes horizon t)

theorem pool_waiting_bound {P : ℕ} (lanes : Fin P → QueueInput) (epoch : Fin P → ℝ)
    (A J S : ℝ) (b horizon : ℕ) (t : ℝ)
    (h : ∀ l, LaneEnvelope (lanes l) (epoch l) A J S) (hburst : J ≤ (b : ℝ) * A) :
    poolWaiting lanes horizon t ≤ P * b := by
  calc
    poolWaiting lanes horizon t ≤ ∑ _l : Fin P, b :=
      Finset.sum_le_sum fun l _ => waiting_card_bound (h l) b horizon t hburst
    _ = P * b := by simp

theorem finite_buffer_no_overflow {P : ℕ} (_hP : 0 < P)
    (lanes : Fin P → QueueInput) (epoch : Fin P → ℝ) (A J S : ℝ)
    (b buffer horizon : ℕ) (t : ℝ)
    (h : ∀ l, LaneEnvelope (lanes l) (epoch l) A J S)
    (hburst : J ≤ (b : ℝ) * A) (hbuffer : P * b ≤ buffer) :
    bufferOverflow lanes buffer horizon t = false := by
  have hc := (pool_waiting_bound lanes epoch A J S b horizon t h hburst).trans hbuffer
  simp [bufferOverflow, not_lt.mpr hc]

/-- Lane l receives global periodic indices P*i+l; full service remains serviceTime. -/
def cyclicLane (P : ℕ) (l : Fin P) (epoch interarrival serviceTime : ℝ) : QueueInput :=
  periodicQueue (epoch + (l : ℕ) * interarrival) ((P : ℝ) * interarrival) serviceTime

theorem cyclic_arrival (P : ℕ) (l : Fin P) (epoch dt S : ℝ) (i : ℕ) :
    (cyclicLane P l epoch dt S).arrival i = epoch + ((P * i + l : ℕ) : ℝ) * dt := by
  simp only [cyclicLane, periodicQueue, Nat.cast_add, Nat.cast_mul]
  ring

theorem cyclic_envelope (P : ℕ) (hP : 0 < P) (l : Fin P) (epoch dt S : ℝ)
    (hdt : 0 < dt) (hS : 0 ≤ S) (hfit : S ≤ (P : ℝ) * dt) :
    LaneEnvelope (cyclicLane P l epoch dt S) (epoch + (l : ℕ) * dt)
      ((P : ℝ) * dt) 0 S := by
  have hA : 0 < (P : ℝ) * dt := mul_pos (by exact_mod_cast hP) hdt
  refine ⟨hA, by norm_num, ?_, ?_, ?_, fun _ => hS, fun _ => le_refl _, hfit, ?_⟩
  · exact (periodicQueue_valid _ _ _ (le_of_lt hA) hS).1
  · intro i; exact le_refl _
  · intro i; simp [cyclicLane, periodicQueue]
  · simp [cyclicLane, periodicQueue]

theorem cyclic_zero_waiting (P : ℕ) (hP : 0 < P) (l : Fin P) (epoch dt S : ℝ)
    (hdt : 0 < dt) (hS : 0 ≤ S) (hfit : S ≤ (P : ℝ) * dt) (i : ℕ) :
    waiting (cyclicLane P l epoch dt S) i = 0 :=
  le_antisymm (waiting_upper (cyclic_envelope P hP l epoch dt S hdt hS hfit) i)
    (waiting_nonnegative _ _)

/-- Nominal rounded milliseconds, not an exact spherical-geometry value.
Unmodeled acquisition, encoding and transport overhead is omitted. -/
def propagationMs : ℝ := 40410046 / 1000000

def routeLatency (q : QueueInput) (i : ℕ) (serialize propagate : ℝ) : ℝ :=
  propagate + serialize + waiting q i + q.service i

def packetLatency (q : QueueInput) (i : ℕ) (serialize : ℝ) : ℝ :=
  routeLatency q i serialize propagationMs

theorem latency_upper {q : QueueInput} {e A J S : ℝ}
    (h : LaneEnvelope q e A J S) (i : ℕ) (serialize propagate : ℝ) :
    routeLatency q i serialize propagate ≤ propagate + serialize + J + S := by
  have hw := waiting_upper h i
  have hs := h.service_upper i
  unfold routeLatency
  linarith

/-- Assumed upper bounds in ms, including a rounded-up propagation bound. -/
theorem conditional_45ms {q : QueueInput} {e A J S : ℝ}
    (h : LaneEnvelope q e A J S) (i : ℕ) (serialize propagate : ℝ)
    (hserial : serialize ≤ 1 / 5) (hjitter : J ≤ 1 / 5) (hservice : S ≤ 4)
    (hpropagate : propagate ≤ 40411 / 1000) :
    routeLatency q i serialize propagate < 45 := by
  have hu := latency_upper h i serialize propagate
  linarith

theorem conditional_fiber_advantage {q : QueueInput} {e A J S : ℝ}
    (h : LaneEnvelope q e A J S) (i : ℕ) (serialize propagate : ℝ)
    (hserial : serialize ≤ 1 / 5) (hjitter : J ≤ 1 / 5) (hservice : S ≤ 4)
    (hpropagate : propagate ≤ 40411 / 1000) :
    routeLatency q i serialize propagate < 77921 / 1000 := by
  have hc := conditional_45ms h i serialize propagate hserial hjitter hservice hpropagate
  linarith

/-- A concrete deterministic envelope witness; these are assumptions, not measured WCET. -/
theorem twenty_lane_example (l : Fin 20) (i : ℕ) :
    waiting (cyclicLane 20 l 0 (1 / 5) 4) i = 0 ∧
      routeLatency (cyclicLane 20 l 0 (1 / 5) 4) i (1 / 5) (40411 / 1000) < 45 := by
  have he := cyclic_envelope 20 (by norm_num) l 0 (1 / 5) 4
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨cyclic_zero_waiting 20 (by norm_num) l 0 (1 / 5) 4
    (by norm_num) (by norm_num) (by norm_num) i,
    conditional_45ms he i _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-- Regardless of the number of parallel lanes, the full service time is still paid. -/
theorem six_ms_service_obstruction (q : QueueInput) (i : ℕ) (serialize : ℝ)
    (hserial : 0 ≤ serialize) (hservice : 6234 / 1000 ≤ q.service i) :
    45 < packetLatency q i serialize := by
  have hw := waiting_nonnegative q i
  unfold packetLatency routeLatency propagationMs
  linarith

theorem throughput_lane_count_example :
    (64 : ℝ) * (96 / 1000) < 6234 / 1000 ∧
      6234 / 1000 ≤ (65 : ℝ) * (96 / 1000) := by norm_num

structure PrometheusPipelinedQueueSuite : Prop where
  wait_bound : ∀ q e A J S, LaneEnvelope q e A J S → ∀ i, waiting q i ≤ J
  sojourn_bound : ∀ q e A J S, LaneEnvelope q e A J S → ∀ i, sojourn q i ≤ J + S
  buffer_bound : ∀ q e A J S, LaneEnvelope q e A J S → ∀ (b horizon : ℕ) (t : ℝ),
    J ≤ (b : ℝ) * A → (waitingSet q horizon t).card ≤ b
  obstruction : ∀ q i serial, 0 ≤ serial → 6234 / 1000 ≤ q.service i →
    45 < packetLatency q i serial

theorem verification_suite : PrometheusPipelinedQueueSuite :=
  ⟨fun _ _ _ _ _ => waiting_upper, fun _ _ _ _ _ => sojourn_upper,
    fun _ _ _ _ _ => waiting_card_bound, six_ms_service_obstruction⟩
end
end PrometheusPipelinedQueue

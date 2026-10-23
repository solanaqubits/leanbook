/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PrometheusVariableQueue

/-! Global packet inputs restricted to a vector of cyclic FIFO lanes.
Service envelopes are hypotheses, never measured WCET. No hardware refinement.
-/
namespace PrometheusMultiLaneQueue
noncomputable section
open PrometheusDecoderQueue PrometheusPipelinedQueue

def laneIndex (M : ℕ) (l : Fin M) (i : ℕ) : ℕ := M * i + l

def lane (M : ℕ) (l : Fin M) (a s : ℕ → ℝ) : QueueInput where
  arrival i := a (laneIndex M l i)
  service i := s (laneIndex M l i)
  initialAvailable := a l

theorem index_reconstruction (M k : ℕ) : M * (k / M) + k % M = k := Nat.div_add_mod k M

theorem global_envelope (M : ℕ) (hM : 0 < M) (l : Fin M) (a s : ℕ → ℝ)
    (epoch dt jitter cap : ℝ) (hdt : 0 < dt) (hj : 0 ≤ jitter)
    (ha : Monotone a) (hlo : ∀ k : ℕ, epoch + (k : ℝ) * dt ≤ a k)
    (hhi : ∀ k : ℕ, a k ≤ epoch + (k : ℝ) * dt + jitter)
    (hs : ∀ k, 0 ≤ s k ∧ s k ≤ cap) (hfit : cap ≤ (M : ℝ) * dt) :
    LaneEnvelope (lane M l a s) (epoch + (l : ℕ) * dt) ((M : ℝ) * dt) jitter cap := by
  refine ⟨mul_pos (by exact_mod_cast hM) hdt, hj, ?_, ?_, ?_, ?_, ?_, hfit, ?_⟩
  · intro i j hij
    apply ha
    unfold laneIndex
    exact Nat.add_le_add_right (Nat.mul_le_mul_left M hij) _
  · intro i
    have h := hlo (laneIndex M l i)
    simp only [lane, laneIndex, Nat.cast_add, Nat.cast_mul] at *
    nlinarith
  · intro i
    have h := hhi (laneIndex M l i)
    simp only [lane, laneIndex, Nat.cast_add, Nat.cast_mul] at *
    nlinarith
  · intro i; exact (hs _).1
  · intro i; exact (hs _).2
  · simp [lane, laneIndex]

theorem vector_wait_buffer (M : ℕ) (hM : 0 < M) (a s : ℕ → ℝ)
    (epoch dt jitter cap : ℝ) (hdt : 0 < dt) (hj : 0 ≤ jitter)
    (ha : Monotone a) (hlo : ∀ k : ℕ, epoch + (k : ℝ) * dt ≤ a k)
    (hhi : ∀ k : ℕ, a k ≤ epoch + (k : ℝ) * dt + jitter)
    (hs : ∀ k, 0 ≤ s k ∧ s k ≤ cap) (hfit : cap ≤ (M : ℝ) * dt)
    (b horizon : ℕ) (t : ℝ) (hb : jitter ≤ (b : ℝ) * ((M : ℝ) * dt)) :
    (∀ l i, waiting (lane M l a s) i ≤ jitter) ∧
      poolWaiting (fun l => lane M l a s) horizon t ≤ M * b := by
  have he := fun l => global_envelope M hM l a s epoch dt jitter cap hdt hj ha hlo hhi hs hfit
  exact ⟨fun l i => waiting_upper (he l) i,
    pool_waiting_bound _ _ _ _ _ b horizon t he hb⟩

theorem periodic_variable_zero (M : ℕ) (hM : 0 < M) (s : ℕ → ℝ)
    (epoch dt cap : ℝ) (hdt : 0 < dt) (hs : ∀ k, 0 ≤ s k ∧ s k ≤ cap)
    (hfit : cap ≤ (M : ℝ) * dt) (l : Fin M) (i : ℕ) :
    waiting (lane M l (fun k => epoch + (k : ℝ) * dt) s) i = 0 := by
  have ha : Monotone (fun k : ℕ => epoch + (k : ℝ) * dt) := by
    intro i j hij
    have h : (i : ℝ) ≤ j := by exact_mod_cast hij
    dsimp
    linarith [mul_le_mul_of_nonneg_right h hdt.le]
  have he := global_envelope M hM l (fun k => epoch + (k : ℝ) * dt) s
    epoch dt 0 cap hdt (by norm_num) ha (fun _ => le_rfl) (fun _ => by simp) hs hfit
  exact le_antisymm (waiting_upper he i) (waiting_nonnegative _ _)

theorem constant_lane (M : ℕ) (l : Fin M) (epoch dt S : ℝ) :
    lane M l (fun k => epoch + (k : ℝ) * dt) (fun _ => S) =
      cyclicLane M l epoch dt S := by
  unfold lane cyclicLane periodicQueue
  congr 1
  funext i
  simp only [laneIndex, Nat.cast_add, Nat.cast_mul]
  ring

/-- Necessity is for a uniform guarantee over every permitted service sequence. -/
theorem uniform_zero_iff (M : ℕ) (hM : 0 < M) (epoch dt cap : ℝ)
    (hdt : 0 < dt) (hc : 0 ≤ cap) :
    (∀ s : ℕ → ℝ, (∀ k, 0 ≤ s k ∧ s k ≤ cap) →
      ∀ l i, waiting (lane M l (fun k => epoch + (k : ℝ) * dt) s) i = 0) ↔
      cap ≤ (M : ℝ) * dt := by
  constructor
  · intro h
    let l : Fin M := ⟨0, hM⟩
    have hz := h (fun _ => cap) (fun _ => ⟨hc, le_rfl⟩) l
    simp only [constant_lane] at hz
    exact (PrometheusVariableQueue.cyclic_threshold M hM l epoch dt cap hdt hc).mp hz
  · intro h s hs l i
    exact periodic_variable_zero M hM s epoch dt cap hdt hs h l i

theorem overload_witness (M : ℕ) (l : Fin M) (epoch dt cap : ℝ)
    (hgap : (M : ℝ) * dt < cap) :
    ∀ bound, ∃ i, bound <
      waiting (lane M l (fun k => epoch + (k : ℝ) * dt) (fun _ => cap)) i := by
  rw [constant_lane]
  exact PrometheusVariableQueue.cyclic_overload M l epoch dt cap hgap

/-- Actual waiting-set cardinality is unbounded, not only packet waiting time. -/
theorem overload_buffer (M : ℕ) (hM : 0 < M) (l : Fin M) (epoch dt cap : ℝ)
    (hdt : 0 < dt) (hgap : (M : ℝ) * dt < cap) (B : ℕ) :
    ∃ horizon t, B < (waitingSet
      (lane M l (fun k => epoch + (k : ℝ) * dt) (fun _ => cap)) horizon t).card := by
  classical
  rw [constant_lane]
  let e : ℝ := epoch + (l : ℕ) * dt
  let A : ℝ := (M : ℝ) * dt
  have hA : 0 < A := mul_pos (by exact_mod_cast hM) hdt
  have hcap : 0 < cap := lt_trans hA hgap
  obtain ⟨i, hi⟩ := periodic_overload_unbounded e A cap hgap ((B : ℝ) * A)
  have hs (j : ℕ) : start (periodicQueue e A cap) j = e + (j : ℝ) * cap := by
    have hw := periodic_overload_waiting e A cap hgap.le j
    unfold waiting periodicQueue at hw
    change start (periodicQueue e A cap) j - (e + (j : ℝ) * A) =
      (j : ℝ) * (cap - A) at hw
    nlinarith
  rw [waiting, hs] at hi
  change (B : ℝ) * A < e + (i : ℝ) * cap - (e + (i : ℝ) * A) at hi
  refine ⟨i+B+1, e + ((i+B : ℕ) : ℝ) * A, ?_⟩
  have hsub : Finset.Icc i (i+B) ⊆ waitingSet (periodicQueue e A cap)
      (i+B+1) (e + ((i+B : ℕ) : ℝ) * A) := by
    intro j hj
    obtain ⟨hij,hji⟩ := Finset.mem_Icc.mp hj
    have hijr : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hjir : (j : ℝ) ≤ (i+B : ℕ) := by exact_mod_cast hji
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_, ?_⟩
    · change e + (j : ℝ) * A ≤ _
      nlinarith
    · rw [hs]
      push_cast at *
      nlinarith
  have hc := Finset.card_le_card hsub
  have hiB : (Finset.Icc i (i+B)).card = B+1 := by simp; omega
  rw [hiB] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self B) hc

def processingDelay (q : QueueInput) (i : ℕ) (serial : ℝ) : ℝ :=
  serial + finish q i - q.arrival i

theorem latency_decomposition (M : ℕ) (l : Fin M) (a s : ℕ → ℝ)
    (i : ℕ) (serial : ℝ) :
    processingDelay (lane M l a s) i serial =
      serial + waiting (lane M l a s) i + s (laneIndex M l i) := by
  unfold processingDelay finish waiting lane
  ring

theorem service_not_divided (M : ℕ) (l : Fin M) (a s : ℕ → ℝ) (i : ℕ) :
    (lane M l a s).service i = s (laneIndex M l i) := rfl

/-- Saturated nominal capacity under the service-cap hypothesis; not achieved goodput. -/
def capacity (M : ℕ) (cap : ℝ) : ℝ := M / cap

theorem capacity_strict (M N : ℕ) (h : M < N) (cap : ℝ) (hc : 0 < cap) :
    capacity M cap < capacity N cap := by
  exact (div_lt_div_iff_of_pos_right hc).mpr (by exact_mod_cast h)

structure PrometheusMultiLaneQueueSuite : Prop where
  uniform : ∀ M, 0 < M → ∀ epoch dt cap, 0 < dt → 0 ≤ cap →
    ((∀ s : ℕ → ℝ, (∀ k, 0 ≤ s k ∧ s k ≤ cap) →
      ∀ l i, waiting (lane M l (fun k => epoch + (k : ℝ) * dt) s) i = 0) ↔
      cap ≤ (M : ℝ) * dt)

theorem verification_suite : PrometheusMultiLaneQueueSuite := ⟨uniform_zero_iff⟩
end
end PrometheusMultiLaneQueue

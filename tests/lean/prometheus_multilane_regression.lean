import Verification.PrometheusMultiLaneQueue
open PrometheusDecoderQueue PrometheusPipelinedQueue PrometheusMultiLaneQueue
example (s : ℕ → ℝ) (hs : ∀ k, 0 ≤ s k ∧ s k ≤ 3072)
    (l : Fin 32) (i : ℕ) :
    waiting (lane 32 l (fun k => (k : ℝ)*96) s) i = 0 := by
  simpa using periodic_variable_zero 32 (by norm_num) s 0 96 3072
    (by norm_num) hs (by norm_num) l i
example : capacity 32 3000 > capacity 16 3000 :=
  capacity_strict 16 32 (by norm_num) 3000 (by norm_num)
example (B : ℕ) : ∃ horizon t, B < (waitingSet
    (lane 1 ⟨0,by norm_num⟩ (fun k => 0+(k : ℝ)*96) (fun _ => 97)) horizon t).card :=
  overload_buffer 1 (by norm_num) ⟨0,by norm_num⟩ 0 96 97
    (by norm_num) (by norm_num) B
example (M : ℕ) (hM : 0 < M) (s : ℕ → ℝ) (a : ℕ → ℝ)
    (dt jitter cap : ℝ) (hdt : 0 < dt) (hj : 0 ≤ jitter) (ha : Monotone a)
    (hl : ∀ k : ℕ, (k : ℝ)*dt ≤ a k)
    (hu : ∀ k : ℕ, a k ≤ (k : ℝ)*dt+jitter)
    (hs : ∀ k, 0 ≤ s k ∧ s k ≤ cap) (hc : cap ≤ (M : ℝ)*dt)
    (b horizon : ℕ) (t : ℝ) (hb : jitter ≤ (b : ℝ)*((M : ℝ)*dt)) :
    poolWaiting (fun l => lane M l a s) horizon t ≤ M*b := by
  exact (vector_wait_buffer M hM a s 0 dt jitter cap hdt hj ha
    (by simpa using hl) (by simpa using hu) hs hc b horizon t hb).2

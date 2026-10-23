import Verification.PrometheusVariableQueue

open PrometheusVariableQueue PrometheusDecoderQueue PrometheusPipelinedQueue

-- Complete before admit: arrivals cannot use service in the same accounting tick.
example : step 2 3 10 empty = ⟨3, 0, 2, 1⟩ := by decide
example : step 2 3 1 ⟨3, 0, 2, 1⟩ = ⟨6, 1, 2, 3⟩ := by decide
example : step 0 3 1 empty = ⟨3, 0, 0, 3⟩ := by decide
example : step 2 0 10 ⟨3, 0, 2, 1⟩ = ⟨3, 2, 0, 1⟩ := by decide
example : run 2 (fun _ => 3) (fun _ => 1) 4 = ⟨12, 3, 2, 7⟩ := by decide
example : run 0 (fun _ => 3) (fun _ => 1) 4 = ⟨12, 0, 0, 12⟩ := by decide
example : run 2 (fun _ => 0) (fun _ => 1) 8 = empty := by decide
example : ¬ Balanced (⟨3, 0, 2, 0⟩ : Counts) := by norm_num [Balanced]
example (c : ℕ) (a s : ℕ → ℕ) (n : ℕ) :
    (run c a s n).offered = (run c a s n).completed +
      (run c a s n).occupancy + (run c a s n).rejected := run_balanced c a s n
example (q : Counts) (h : Balanced q) (n : ℕ)
    (ha : (3 : ℝ) * n ≤ q.offered) (hs : (q.completed : ℝ) ≤ n)
    (hc : q.occupancy ≤ 2) : (2 : ℝ) * n - 2 ≤ q.rejected := by
  convert finite_capacity_loss_lower q h 2 n hc 3 1 0 ha (by simpa using hs) using 1
  norm_num
example (q : ℕ → Counts) (hb : ∀ n, Balanced (q n))
    (hc : ∀ n, (q n).occupancy ≤ 2)
    (ha : ∀ n, (3 : ℝ) * n ≤ (q n).offered)
    (hs : ∀ n, ((q n).completed : ℝ) ≤ n) :
    ∀ bound : ℝ, ∃ n, bound < ((q n).rejected : ℝ) :=
  finite_capacity_unbounded_loss q 2 3 1 0 (by norm_num) hb hc ha (by simpa using hs)
example (q : ℕ → Counts) (hb : ∀ n, Balanced (q n))
    (hl : ∀ n, (q n).rejected = 0)
    (ha : ∀ n, (3 : ℝ) * n ≤ (q n).offered)
    (hs : ∀ n, ((q n).completed : ℝ) ≤ n) :
    ∀ bound : ℝ, ∃ n, bound < ((q n).occupancy : ℝ) :=
  no_loss_unbounded_occupancy q 3 1 0 (by norm_num) hb hl ha (by simpa using hs)
-- At equality no waiting for this initially idle constant periodic cyclic system.
example (l : Fin 4) : ∀ i, waiting (cyclicLane 4 l 0 2 8) i = 0 :=
  (cyclic_threshold 4 (by norm_num) l 0 2 8 (by norm_num) (by norm_num)).mpr (by norm_num)
example (l : Fin 4) : ∀ bound, ∃ i, bound < waiting (cyclicLane 4 l 0 2 9) i :=
  cyclic_overload 4 l 0 2 9 (by norm_num)
example (l : Fin 4) : ¬ (∀ i, waiting (cyclicLane 4 l 0 2 9) i = 0) := by
  rw [cyclic_threshold 4 (by norm_num) l 0 2 9 (by norm_num) (by norm_num)]
  norm_num
example : (8 : ℝ) / (4 * 2) = 1 := by norm_num
example (dt s : ℝ) (hdt : 0 < dt) : s / ((4 : ℝ) * dt) ≤ 1 ↔ s ≤ 4 * dt :=
  load_threshold 4 (by norm_num) dt s hdt

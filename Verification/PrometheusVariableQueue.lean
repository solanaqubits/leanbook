/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PrometheusPipelinedQueue

/-!
# Variable-input accounting and overload

The event model completes up to `service` jobs already in the system, then admits
new arrivals up to total capacity (waiting plus in-service). It is an accounting
abstraction, not a CPU scheduler refinement. Cumulative rate envelopes are explicit
premises. Constant cyclic FIFO lanes reuse epsilon250/253 for an exact threshold;
empirical medians do not supply any of these service bounds.
-/
namespace PrometheusVariableQueue
open PrometheusDecoderQueue PrometheusPipelinedQueue
noncomputable section

structure Counts where
  offered : ℕ
  completed : ℕ
  occupancy : ℕ
  rejected : ℕ
  deriving DecidableEq, Repr

def empty : Counts := ⟨0, 0, 0, 0⟩
def Balanced (q : Counts) : Prop := q.offered = q.completed + q.occupancy + q.rejected

/-- Complete before admit; `capacity` includes jobs in service. -/
def step (capacity arrivals service : ℕ) (q : Counts) : Counts :=
  let done := min service q.occupancy
  let remaining := q.occupancy - done
  let accepted := min arrivals (capacity - remaining)
  ⟨q.offered + arrivals, q.completed + done, remaining + accepted,
    q.rejected + (arrivals - accepted)⟩

theorem empty_balanced : Balanced empty := rfl

theorem step_balanced (capacity arrivals service : ℕ) (q : Counts) (h : Balanced q) :
    Balanced (step capacity arrivals service q) := by
  have hd := Nat.min_le_right service q.occupancy
  have ha := Nat.min_le_left arrivals (capacity - (q.occupancy - min service q.occupancy))
  unfold Balanced step at *
  dsimp at *
  omega

theorem step_capacity (capacity arrivals service : ℕ) (q : Counts)
    (h : q.occupancy ≤ capacity) : (step capacity arrivals service q).occupancy ≤ capacity := by
  have hd := Nat.min_le_right service q.occupancy
  have ha := Nat.min_le_right arrivals (capacity - (q.occupancy - min service q.occupancy))
  simp only [step]
  omega

def run (capacity : ℕ) (arrivals service : ℕ → ℕ) : ℕ → Counts
  | 0 => empty
  | n + 1 => step capacity (arrivals n) (service n) (run capacity arrivals service n)

theorem run_balanced (capacity : ℕ) (arrivals service : ℕ → ℕ) :
    ∀ n, Balanced (run capacity arrivals service n) := by
  intro n
  induction n with
  | zero => exact empty_balanced
  | succ n ih => exact step_balanced _ _ _ _ ih

theorem run_capacity (capacity : ℕ) (arrivals service : ℕ → ℕ) :
    ∀ n, (run capacity arrivals service n).occupancy ≤ capacity := by
  intro n
  induction n with
  | zero => simp [run, empty]
  | succ n ih => exact step_capacity _ _ _ _ ih

/-- A lower bound on offered work and upper bound on completions imply overload.
No stationarity, independence or measured median is hidden in the premises. -/
theorem cumulative_excess (q : Counts) (h : Balanced q) (n : ℕ)
    (arrivalRate serviceRate burst : ℝ)
    (ha : arrivalRate * n ≤ q.offered)
    (hs : (q.completed : ℝ) ≤ serviceRate * n + burst) :
    (arrivalRate - serviceRate) * n - burst ≤ (q.occupancy : ℝ) + q.rejected := by
  have hb : (q.offered : ℝ) = (q.completed : ℝ) + q.occupancy + q.rejected := by
    exact_mod_cast h
  linarith

theorem finite_capacity_loss_lower (q : Counts) (h : Balanced q) (capacity n : ℕ)
    (hc : q.occupancy ≤ capacity) (arrivalRate serviceRate burst : ℝ)
    (ha : arrivalRate * n ≤ q.offered)
    (hs : (q.completed : ℝ) ≤ serviceRate * n + burst) :
    (arrivalRate - serviceRate) * n - burst - capacity ≤ (q.rejected : ℝ) := by
  have he := cumulative_excess q h n arrivalRate serviceRate burst ha hs
  have hcr : (q.occupancy : ℝ) ≤ capacity := by exact_mod_cast hc
  linarith

/-- Positive cumulative excess cannot be absorbed by any fixed finite capacity. -/
theorem finite_capacity_unbounded_loss (q : ℕ → Counts) (capacity : ℕ)
    (arrivalRate serviceRate burst : ℝ) (hgap : serviceRate < arrivalRate)
    (hb : ∀ n, Balanced (q n)) (hc : ∀ n, (q n).occupancy ≤ capacity)
    (ha : ∀ n, arrivalRate * n ≤ (q n).offered)
    (hs : ∀ n, ((q n).completed : ℝ) ≤ serviceRate * n + burst) :
    ∀ bound : ℝ, ∃ n, bound < ((q n).rejected : ℝ) := by
  intro bound
  obtain ⟨n, hn⟩ := exists_nat_gt ((bound + burst + capacity) / (arrivalRate - serviceRate))
  have hp : 0 < arrivalRate - serviceRate := sub_pos.mpr hgap
  have hn' : bound + burst + capacity < (n : ℝ) * (arrivalRate - serviceRate) :=
    (div_lt_iff₀ hp).mp hn
  have hl := finite_capacity_loss_lower (q n) (hb n) capacity n (hc n)
    arrivalRate serviceRate burst (ha n) (hs n)
  refine ⟨n, ?_⟩
  nlinarith

/-- In a no-loss system the same excess must accumulate in occupancy. -/
theorem no_loss_unbounded_occupancy (q : ℕ → Counts)
    (arrivalRate serviceRate burst : ℝ) (hgap : serviceRate < arrivalRate)
    (hb : ∀ n, Balanced (q n)) (hl : ∀ n, (q n).rejected = 0)
    (ha : ∀ n, arrivalRate * n ≤ (q n).offered)
    (hs : ∀ n, ((q n).completed : ℝ) ≤ serviceRate * n + burst) :
    ∀ bound : ℝ, ∃ n, bound < ((q n).occupancy : ℝ) := by
  intro bound
  obtain ⟨n, hn⟩ := exists_nat_gt ((bound + burst) / (arrivalRate - serviceRate))
  have hp : 0 < arrivalRate - serviceRate := sub_pos.mpr hgap
  have hn' := (div_lt_iff₀ hp).mp hn
  have he := cumulative_excess (q n) (hb n) n arrivalRate serviceRate burst (ha n) (hs n)
  rw [hl n] at he
  push_cast at he
  refine ⟨n, ?_⟩
  nlinarith

/-- For initially idle cyclic FIFO lanes this includes the equality boundary. -/
theorem cyclic_threshold (P : ℕ) (hP : 0 < P) (l : Fin P) (epoch dt service : ℝ)
    (hdt : 0 < dt) (hservice : 0 ≤ service) :
    (∀ i, waiting (cyclicLane P l epoch dt service) i = 0) ↔ service ≤ (P : ℝ) * dt := by
  constructor
  · intro h
    by_contra hn
    have hu := periodic_overload_unbounded (epoch + (l : ℕ) * dt) ((P : ℝ) * dt)
      service (lt_of_not_ge hn) 0
    obtain ⟨i, hi⟩ := hu
    change 0 < waiting (cyclicLane P l epoch dt service) i at hi
    rw [h i] at hi
    exact lt_irrefl _ hi
  · intro h i
    exact cyclic_zero_waiting P hP l epoch dt service hdt hservice h i

theorem cyclic_overload (P : ℕ) (l : Fin P) (epoch dt service : ℝ)
    (h : (P : ℝ) * dt < service) :
    ∀ bound, ∃ i, bound < waiting (cyclicLane P l epoch dt service) i :=
  periodic_overload_unbounded _ _ _ h

/-- Dimensionless load; requires a positive worker count and positive spacing. -/
theorem load_threshold (P : ℕ) (hP : 0 < P) (dt service : ℝ) (hdt : 0 < dt) :
    service / ((P : ℝ) * dt) ≤ 1 ↔ service ≤ (P : ℝ) * dt := by
  have hp : 0 < (P : ℝ) * dt := mul_pos (by exact_mod_cast hP) hdt
  rw [div_le_iff₀ hp]
  simp

structure PrometheusVariableQueueSuite : Prop where
  conservation : ∀ capacity arrivals service n, Balanced (run capacity arrivals service n)
  capacity : ∀ capacity arrivals service n, (run capacity arrivals service n).occupancy ≤ capacity
  excess : ∀ q, Balanced q → ∀ (n : ℕ) (a s b : ℝ), a * n ≤ q.offered →
    (q.completed : ℝ) ≤ s * n + b → (a - s) * n - b ≤ (q.occupancy : ℝ) + q.rejected
  threshold : ∀ P, 0 < P → ∀ (l : Fin P) epoch dt service, 0 < dt → 0 ≤ service →
    ((∀ i, waiting (cyclicLane P l epoch dt service) i = 0) ↔ service ≤ (P : ℝ) * dt)

theorem verification_suite : PrometheusVariableQueueSuite :=
  ⟨run_balanced, run_capacity, cumulative_excess, cyclic_threshold⟩
end
end PrometheusVariableQueue

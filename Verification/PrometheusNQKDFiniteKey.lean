/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Conditional scalar finite-key bookkeeping. Serfling sampling and the quantum
entropy/LHL bridge are explicit theorem premises, NOT proved protocol security.
Authentication key consumption is not raw-key leakage. No physical NQKD claim. -/
namespace PrometheusNQKDFiniteKey
noncomputable section

def bits (A : ℝ) : ℤ := max 0 ⌊A⌋

theorem bits_positive_iff (A : ℝ) : 0 < bits A ↔ 1 ≤ A := by
  simp only [bits, lt_max_iff, lt_self_iff_false, false_or]
  simpa using (Int.lt_floor_iff (a := A) (z := 0))

theorem half_bit_counterexample : (0 : ℝ) < 1/2 ∧ bits (1/2) = 0 := by
  norm_num [bits]

def budget (n entropy leakage penalty : ℝ) : ℝ := n * (1-entropy) - leakage - penalty

theorem positive_rate_iff (n h L P : ℝ) (hn : 0 < n) :
    0 < bits (budget n h L P) ↔ (L+P+1)/n ≤ 1-h := by
  rw [bits_positive_iff, div_le_iff₀ hn]
  unfold budget
  constructor <;> intro hs <;> nlinarith

def binaryEntropy (q : ℝ) : ℝ := -(q * Real.log q + (1-q)*Real.log (1-q))/Real.log 2

theorem entropy_one : binaryEntropy 1 = 0 := by simp [binaryEntropy]

def publicLeak (syndrome verify decision : ℕ) : ℕ := syndrome + verify + decision

theorem historical_leak : publicLeak 301 64 1 = 366 := by norm_num [publicLeak]

/-- Key consumption is deducted from expansion, not from the public transcript twice. -/
def netExpansion (length authCost : ℕ) : ℕ := length - authCost

theorem net_le_output (length cost : ℕ) : netExpansion length cost ≤ length := Nat.sub_le _ _

def admissible (q : ℝ) (authenticated verified : Bool) : Prop :=
  0 ≤ q ∧ q < 1/2 ∧ authenticated = true ∧ verified = true

def outputBits (q A : ℝ) (authenticated verified : Bool) : ℤ := by
  classical
  exact if admissible q authenticated verified then bits A else 0

theorem abort_phase (q A : ℝ) (a v : Bool) (hq : 1 / 2 ≤ q) : outputBits q A a v = 0 := by
  have hn : ¬ admissible q a v := fun h => (not_lt_of_ge hq) h.2.1
  simp [outputBits, hn]

theorem abort_no_auth (q A : ℝ) (v : Bool) : outputBits q A false v = 0 := by
  simp [outputBits, admissible]

theorem abort_failed_verification (q A : ℝ) (a : Bool) : outputBits q A a false = 0 := by
  simp [outputBits, admissible]

theorem output_positive_iff (q A : ℝ) (a v : Bool) :
    0 < outputBits q A a v ↔ admissible q a v ∧ 1 ≤ A := by
  by_cases h : admissible q a v <;> simp [outputBits, h, bits_positive_iff]

theorem no_entropy_budget (n h L P : ℝ) (hn : 0 ≤ n) (hh : 1 ≤ h)
    (hL : 0 ≤ L) (hP : 0 ≤ P) : bits (budget n h L P) = 0 := by
  have hb : budget n h L P ≤ 0 := by unfold budget; nlinarith
  have hf : ⌊budget n h L P⌋ ≤ (0 : ℤ) := by
    have := Int.floor_le (budget n h L P)
    exact_mod_cast le_trans this hb
  exact max_eq_left hf

/-- Classical tail coefficient for a random split with retained n and tested m.
The validity of its probability bound is an external sampling premise. -/
def coefficient (n m : ℝ) : ℝ := 2*n*m^2/((n+m)*(m+1))

theorem coefficient_pos (n m : ℝ) (hn : 0 < n) (hm : 0 < m) : 0 < coefficient n m := by
  unfold coefficient
  positivity

def slack (a eps : ℝ) : ℝ := Real.sqrt (Real.log (1/eps)/a)

theorem slack_square (a eps : ℝ) (ha : 0 < a) (he : 0 < eps) (he1 : eps ≤ 1) :
    a * slack a eps ^ 2 = Real.log (1/eps) := by
  have hlog : 0 ≤ Real.log (1/eps) := Real.log_nonneg ((le_div_iff₀ he).mpr (by simpa using he1))
  rw [slack, Real.sq_sqrt (div_nonneg hlog ha.le)]
  field_simp

theorem tail_at_slack (a eps : ℝ) (ha : 0 < a) (he : 0 < eps) (he1 : eps ≤ 1) :
    Real.exp (-a * slack a eps ^ 2) = eps := by
  have h := slack_square a eps ha he he1
  rw [neg_mul, h, Real.exp_neg, Real.exp_log (div_pos one_pos he)]
  field_simp

/-- A conditional consequence; this does not prove Serfling's sampling theorem. -/
theorem conditional_sampling_tail (p a eps : ℝ) (ha : 0 < a) (he : 0 < eps)
    (he1 : eps ≤ 1) (sampling : p ≤ Real.exp (-a * slack a eps ^ 2)) : p ≤ eps := by
  rw [tail_at_slack a eps ha he he1] at sampling
  exact sampling

theorem conditioned_tail (bad pass eps : ℝ) (hpass : 0 < pass) (hbad : bad ≤ eps) :
    bad / pass ≤ eps / pass := (div_le_div_iff_of_pos_right hpass).mpr hbad

/-- Direct scalar LHL residual. The relation to quantum trace distance is a premise. -/
def hashResidual (ell H : ℝ) : ℝ := Real.exp ((ell-H)*Real.log 2/2)/2

def paPenalty (eps : ℝ) : ℝ := 2 * Real.log (1/(2*eps)) / Real.log 2

theorem hash_residual_bound (ell H eps : ℝ) (he : 0 < eps)
    (budget_bound : ell ≤ H - paPenalty eps) : hashResidual ell H ≤ eps := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne : Real.log (1/(2*eps)) = -Real.log (2*eps) := by
    rw [one_div, Real.log_inv]
  have hb : (ell-H)*Real.log 2/2 ≤ Real.log (2*eps) := by
    unfold paPenalty at budget_bound
    rw [hne] at budget_bound
    have hb0 : ell-H ≤ (2 * Real.log (2*eps)) / Real.log 2 := by
      simp only [mul_neg, neg_div] at budget_bound
      linarith
    have h := (le_div_iff₀ hl).mp hb0
    nlinarith
  unfold hashResidual
  have h := Real.exp_le_exp.mpr hb
  rw [Real.exp_log (by positivity : 0 < 2*eps)] at h
  linarith

theorem integer_extraction_bound (H eps : ℝ) (he : 0 < eps)
    (hbudget : 1 ≤ H - paPenalty eps) :
    hashResidual (bits (H - paPenalty eps)) H ≤ eps := by
  have hf : 0 ≤ ⌊H - paPenalty eps⌋ := by
    exact Int.floor_nonneg.mpr (by linarith)
  have hb : bits (H - paPenalty eps) = ⌊H - paPenalty eps⌋ := max_eq_right hf
  rw [hb]
  exact hash_residual_bound _ _ _ he (Int.floor_le _)

theorem conditional_secrecy (distance smooth pa secrecy : ℝ)
    (LHL : distance ≤ 2 * smooth + pa) (allocation : 2 * smooth + pa ≤ secrecy) :
    distance ≤ secrecy := LHL.trans allocation

theorem fixed_allocation :
    2 * (1/40000000000 : ℝ) + 1/20000000000 = 1/10000000000 := by norm_num

theorem pe_is_square : (1/40000000000 : ℝ)^2 = 1/1600000000000000000000 := by norm_num

structure PrometheusNQKDFiniteKeySuite : Prop where
  integer_threshold : ∀ A : ℝ, 0 < bits A ↔ 1 ≤ A
  auth_guard : ∀ q A : ℝ, ∀ v : Bool, outputBits q A false v = 0
  phase_guard : ∀ q A : ℝ, ∀ a v : Bool, 1 / 2 ≤ q → outputBits q A a v = 0
  extraction_bound : ∀ ell H eps : ℝ, 0 < eps → ell ≤ H - paPenalty eps → hashResidual ell H ≤ eps

theorem verification_suite : PrometheusNQKDFiniteKeySuite :=
  ⟨bits_positive_iff, abort_no_auth, abort_phase, hash_residual_bound⟩
end
end PrometheusNQKDFiniteKey

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoHiddenScalarForkAcquisitionContract
import Verification.CryptoBulletproofsIPABoundedRetryContract

/-! Conditional quota progress for the actual finite collector. No independence,
external process refinement, global density or complexity claim. -/
namespace CryptoHiddenScalarForkProgressProbabilityContract
open scoped BigOperators
open CryptoHiddenScalarForkAcquisitionContract
namespace Prob
export CryptoBulletproofsIPATreeProbabilityContract (probability probability_mono)
end Prob

section Scan
variable {I V K : Type} [DecidableEq K]

/-- Successful values must carry the candidate's key; generic Attempt does not
impose this law, whereas the concrete snapshot collectors construct it. -/
def KeyCoherent (label : I → K) (key : V → K) (attempt : I → Attempt V) : Prop :=
  ∀ i v, (attempt i).value = some v → key v = label i

theorem scan_full (n : ℕ) (label : I → K) (key : V → K) (attempt : I → Attempt V)
    (xs : List I) (acc : List V) (h : acc.length = n) :
    (scan n label key attempt xs acc).1 = acc := by
  cases xs <;> simp [scan, h]

theorem scan_append (n : ℕ) (label : I → K) (key : V → K) (attempt : I → Attempt V)
    (xs ys : List I) (acc : List V) :
    (scan n label key attempt (xs ++ ys) acc).1 =
      (scan n label key attempt ys (scan n label key attempt xs acc).1).1 := by
  induction xs generalizing acc with
  | nil => simp only [List.nil_append, scan]; split <;> rfl
  | cons i xs ih =>
    by_cases h : acc.length = n
    · simp [scan, h, scan_full n label key attempt ys acc h]
    by_cases hd : label i ∈ acc.map key
    · simpa [scan, h, hd] using ih acc
    · cases hv : (attempt i).value <;> simpa [scan, h, hd, hv] using ih _

theorem scan_invariants (n : ℕ) (label : I → K) (key : V → K) (attempt : I → Attempt V)
    (hc : KeyCoherent label key attempt) (xs : List I) (acc : List V)
    (hl : acc.length ≤ n) (hd : (acc.map key).Nodup) :
    (scan n label key attempt xs acc).1.length ≤ n ∧
      ((scan n label key attempt xs acc).1.map key).Nodup := by
  induction xs generalizing acc with
  | nil => simp only [scan]; split <;> exact ⟨hl, hd⟩
  | cons i xs ih =>
    by_cases h : acc.length = n
    · simp [scan, h, hd]
    by_cases hi : label i ∈ acc.map key
    · simpa [scan, h, hi] using ih acc hl hd
    cases hv : (attempt i).value with
    | none => simpa [scan, h, hi, hv] using ih acc hl hd
    | some v =>
      have hk := hc i v hv
      have hlen : (acc ++ [v]).length ≤ n := by
        simp only [List.length_append, List.length_singleton]
        omega
      have hdup : ((acc ++ [v]).map key).Nodup := by
        rw [List.map_append, List.map_singleton, hk, List.nodup_append_comm]
        exact List.nodup_cons.mpr ⟨hi, hd⟩
      simpa [scan, h, hi, hv] using ih (acc ++ [v]) hlen hdup

def retainedCount (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (xs : List I) (i : ℕ) : ℕ :=
  (scan n label key attempt (xs.take i) []).1.length

@[simp] theorem retained_zero (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (xs : List I) : retainedCount n label key attempt xs 0 = 0 := by
  simp [retainedCount, scan]; split <;> rfl

theorem retained_le (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (hc : KeyCoherent label key attempt) (xs : List I) (i : ℕ) :
    retainedCount n label key attempt xs i ≤ n :=
  (scan_invariants n label key attempt hc (xs.take i) [] (Nat.zero_le _) (by simp)).1

theorem retained_step (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (xs : List I) (i : ℕ) :
    retainedCount n label key attempt xs (i + 1) = retainedCount n label key attempt xs i ∨
    retainedCount n label key attempt xs (i + 1) = retainedCount n label key attempt xs i + 1 := by
  by_cases h : i < xs.length
  · have ht : xs.take (i + 1) = xs.take i ++ [xs[i]] := List.take_succ_eq_append_getElem h
    unfold retainedCount
    rw [ht, scan_append]
    generalize (scan n label key attempt (xs.take i) []).1 = acc
    simp only [scan]
    split
    · exact Or.inl rfl
    · split
      · simp
      · cases (attempt xs[i]).value with
        | none => split <;> split_ifs <;> simp_all
        | some v => split <;> split_ifs <;> simp_all
  · have hle : xs.length ≤ i := by omega
    simp [retainedCount, List.take_of_length_le hle,
      List.take_of_length_le (show xs.length ≤ i + 1 by omega)]

theorem select_isSome_iff (n : ℕ) (key : V → K) (xs : List V)
    (hd : (xs.map key).Nodup) : (select n key xs).isSome = true ↔ xs.length = n := by
  constructor
  · intro h
    by_contra hn
    simp [select, hn] at h
  · intro h
    exact select_success n key xs h hd

theorem collect_success_iff_quota (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (hc : KeyCoherent label key attempt) (xs : List I) :
    (collect n label key attempt xs).value.isSome = true ↔
      retainedCount n label key attempt xs xs.length = n := by
  have hd := (scan_invariants n label key attempt hc xs [] (Nat.zero_le _) (by simp)).2
  simpa [collect, retainedCount] using select_isSome_iff n key _ hd
end Scan

/-- Finite-horizon reference birth process, absorbing at the quota. -/
def quotaLower (n : ℕ) (p : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0, j => if n ≤ j then 1 else 0
  | b + 1, j => if n ≤ j then 1 else
      (1 - p j) * quotaLower n p b j + p j * quotaLower n p b (j + 1)

@[simp] theorem quota_full (n : ℕ) (p : ℕ → ℚ) (b j : ℕ) (h : n ≤ j) :
    quotaLower n p b j = 1 := by cases b <;> simp [quotaLower, h]

theorem quota_bounds (n : ℕ) (p : ℕ → ℚ)
    (hp : ∀ j < n, 0 ≤ p j ∧ p j ≤ 1) (b j : ℕ) :
    0 ≤ quotaLower n p b j ∧ quotaLower n p b j ≤ 1 := by
  induction b generalizing j with
  | zero => simp only [quotaLower]; split <;> norm_num
  | succ b ih =>
    by_cases h : n ≤ j
    · simp [quotaLower, h]
    have hj : j < n := by omega
    obtain ⟨h0,h1⟩ := hp j hj
    obtain ⟨a0,a1⟩ := ih j
    obtain ⟨b0,b1⟩ := ih (j + 1)
    rw [quotaLower, if_neg h]
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) a0) (mul_nonneg h0 b0)
    · nlinarith [mul_nonneg
        (show 0 ≤ 1 - p j by linarith) (show 0 ≤ 1-quotaLower n p b j by linarith),
        mul_nonneg h0 (show 0 ≤ 1-quotaLower n p b (j + 1) by linarith)]

theorem quota_step_mono (n : ℕ) (p : ℕ → ℚ)
    (hp : ∀ j < n, 0 ≤ p j ∧ p j ≤ 1) (b j : ℕ) :
    quotaLower n p b j ≤ quotaLower n p b (j + 1) := by
  induction b generalizing j with
  | zero =>
    simp only [quotaLower]
    split_ifs <;> norm_num
    omega
  | succ b ih =>
    by_cases h : n ≤ j
    · simp [quota_full n p (b + 1) j h, quota_full n p (b + 1) (j + 1) (by omega)]
    by_cases h' : n ≤ j + 1
    · rw [quota_full n p (b + 1) (j + 1) h']
      exact (quota_bounds n p hp (b + 1) j).2
    have hj := hp j (by omega)
    have hj' := hp (j + 1) (by omega)
    rw [quotaLower, if_neg h, quotaLower, if_neg h']
    nlinarith [mul_nonneg (show 0 ≤ 1 - p j by linarith) (sub_nonneg.mpr (ih j)),
      mul_nonneg hj'.1 (sub_nonneg.mpr (ih (j + 1)))]

/-- Laws for the actual retained-count process, not a Markov assumption. -/
def CountLaws {Seed : Type} (D : Finset Seed) (N : ℕ → Seed → ℕ) (n T : ℕ) : Prop :=
  (∀ w ∈ D, N 0 w = 0) ∧ (∀ i ≤ T, ∀ w ∈ D, N i w ≤ n) ∧
  (∀ i < T, ∀ w ∈ D, N (i + 1) w = N i w ∨ N (i + 1) w = N i w + 1)

/-- Cardinality form avoids conditioning on empty histories. Aggregate state
bounds suffice; stronger full-history bounds can be summed to obtain them. -/
def ProgressBounds {Seed : Type} [DecidableEq Seed] (D : Finset Seed)
    (N : ℕ → Seed → ℕ) (n T : ℕ) (p : ℕ → ℚ) : Prop :=
  (∀ j < n, 0 ≤ p j ∧ p j ≤ 1) ∧ ∀ i < T, ∀ j < n,
    p j * (D.filter (fun w => N i w = j)).card ≤
      ((D.filter (fun w => N i w = j ∧ N (i + 1) w = j + 1)).card : ℚ)

instance progressBoundsDecidable {Seed : Type} [DecidableEq Seed] (D : Finset Seed)
    (N : ℕ → Seed → ℕ) (n T : ℕ) (p : ℕ → ℚ) : Decidable (ProgressBounds D N n T p) := by
  unfold ProgressBounds
  infer_instance


section Probability
variable {Seed : Type} [DecidableEq Seed]

omit [DecidableEq Seed] in
private theorem sum_by_count (D : Finset Seed) (N : Seed → ℕ) (n : ℕ)
    (hn : ∀ w ∈ D, N w ≤ n) (f : Seed → ℚ) :
    (∑ j ∈ Finset.range (n + 1), ∑ w ∈ D.filter (fun w => N w = j), f w) = ∑ w ∈ D, f w := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  simp [Finset.mem_range, Nat.lt_succ_of_le (hn w hw)]

omit [DecidableEq Seed] in
private theorem fiber_drift (D : Finset Seed) (N : ℕ → Seed → ℕ) (n i b : ℕ)
    (p : ℕ → ℚ) (hp : ∀ j < n, 0 ≤ p j ∧ p j ≤ 1)
    (hn : ∀ w ∈ D, N (i + 1) w ≤ n)
    (hs : ∀ w ∈ D, N (i + 1) w = N i w ∨ N (i + 1) w = N i w + 1)
    (hd : ∀ j < n, p j * (D.filter (fun w => N i w = j)).card ≤
      ((D.filter (fun w => N i w = j ∧ N (i + 1) w = j + 1)).card : ℚ))
    (j : ℕ) (hj : j ≤ n) :
    (∑ w ∈ D.filter (fun w => N i w = j), quotaLower n p (b + 1) (N i w)) ≤
    ∑ w ∈ D.filter (fun w => N i w = j), quotaLower n p b (N (i + 1) w) := by
  let E := D.filter (fun w => N i w = j)
  have he : ∀ w ∈ E, w ∈ D ∧ N i w = j := fun w hw => Finset.mem_filter.mp hw
  have hleft : (∑ w ∈ E, quotaLower n p (b + 1) (N i w)) =
      E.card * quotaLower n p (b + 1) j := by
    calc
      _ = ∑ _w ∈ E, quotaLower n p (b + 1) j :=
        Finset.sum_congr rfl (fun w hw => by rw [(he w hw).2])
      _ = _ := by simp
  change (∑ w ∈ E, _) ≤ ∑ w ∈ E, _
  rw [hleft]
  by_cases hfull : n ≤ j
  · have heq : j = n := by omega
    have hnext : ∀ w ∈ E, N (i + 1) w = n := by
      intro w hw
      have hstep := hs w (he w hw).1
      have hb := hn w (he w hw).1
      have hprev := (he w hw).2
      omega
    rw [quota_full n p (b + 1) j hfull]
    simp_rw [mul_one]
    calc
      (E.card : ℚ) = ∑ _w ∈ E, (1 : ℚ) := by simp
      _ ≤ ∑ w ∈ E, quotaLower n p b (N (i + 1) w) := le_of_eq
        (Finset.sum_congr rfl (fun w hw => by rw [hnext w hw, quota_full n p b n le_rfl]))
  · have hj' : j < n := by omega
    let S := E.filter (fun w => N (i + 1) w = j + 1)
    have hS : S = D.filter (fun w => N i w = j ∧ N (i + 1) w = j + 1) := by
      ext w; simp [S, E, and_assoc]
    have hsum : (∑ w ∈ E, quotaLower n p b (N (i + 1) w)) =
        E.card * quotaLower n p b j + S.card * (quotaLower n p b (j + 1) - quotaLower n p b j) := by
      calc
        _ = ∑ w ∈ E, (quotaLower n p b j + if N (i + 1) w = j + 1 then
            quotaLower n p b (j + 1) - quotaLower n p b j else 0) := by
          apply Finset.sum_congr rfl
          intro w hw
          obtain ha | ha := hs w (he w hw).1
          · rw [ha, (he w hw).2]; simp
          · rw [ha, (he w hw).2]; simp
        _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_filter, S, mul_sub]
    rw [hsum, quotaLower, if_neg hfull]
    have hprogress : p j * E.card ≤ (S.card : ℚ) := by simpa [E, hS] using hd j hj'
    have hmono := quota_step_mono n p hp b j
    nlinarith [mul_le_mul_of_nonneg_right hprogress (sub_nonneg.mpr hmono)]

private theorem potential_drift (D : Finset Seed) (N : ℕ → Seed → ℕ) (n T i b : ℕ)
    (p : ℕ → ℚ) (hl : CountLaws D N n T) (hp : ProgressBounds D N n T p) (hi : i < T) :
    (∑ w ∈ D, quotaLower n p (b + 1) (N i w)) ≤
      ∑ w ∈ D, quotaLower n p b (N (i + 1) w) := by
  rw [← sum_by_count D (N i) n (hl.2.1 i (by omega)) (fun w => quotaLower n p (b + 1) (N i w)),
    ← sum_by_count D (N i) n (hl.2.1 i (by omega)) (fun w => quotaLower n p b (N (i + 1) w))]
  apply Finset.sum_le_sum
  intro j hj
  exact fiber_drift D N n i b p hp.1 (hl.2.1 (i + 1) (by omega))
    (hl.2.2 i hi) (hp.2 i hi) j (by simpa using hj)

/-- Lower bound for a skip-free retained-count process. The actual process may
be correlated and non-Markovian; only the stated conditional masses are used. -/
theorem quota_probability_lower (D : Finset Seed) (hD : D.Nonempty)
    (N : ℕ → Seed → ℕ) (n T : ℕ) (p : ℕ → ℚ)
    (hl : CountLaws D N n T) (hp : ProgressBounds D N n T p) :
    quotaLower n p T 0 ≤ Prob.probability D (D.filter (fun w => N T w = n)) := by
  have hpot : ∀ i ≤ T, (D.card : ℚ) * quotaLower n p T 0 ≤
      ∑ w ∈ D, quotaLower n p (T-i) (N i w) := by
    intro i
    induction i with
    | zero =>
      intro _
      have he : (∑ w ∈ D, quotaLower n p T (N 0 w)) = D.card * quotaLower n p T 0 := by
        calc
          _ = ∑ _w ∈ D, quotaLower n p T 0 := Finset.sum_congr rfl (fun w hw => by rw [hl.1 w hw])
          _ = _ := by simp
      simpa using le_of_eq he.symm
    | succ i ih =>
      intro hi
      have h := potential_drift D N n T i (T - (i + 1)) p hl hp (by omega)
      have he : T-i = T - (i + 1) + 1 := by omega
      exact (ih (by omega)).trans (by simpa only [he] using h)
  have hfinal := hpot T le_rfl
  have he : (∑ w ∈ D, quotaLower n p (T-T) (N T w)) =
      ((D.filter fun w => N T w = n).card : ℚ) := by
    simp only [Nat.sub_self, quotaLower]
    have hh : ∀ w ∈ D, (n ≤ N T w) ↔ N T w = n := by
      intro w hw; have := hl.2.1 T le_rfl w hw; omega
    calc
      _ = ∑ w ∈ D, if N T w = n then (1 : ℚ) else 0 :=
        Finset.sum_congr rfl (fun w hw => by simp only [hh w hw])
      _ = _ := by simp
  rw [he] at hfinal
  have hc : (0 : ℚ) < D.card := by exact_mod_cast hD.card_pos
  unfold Prob.probability
  rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
  apply (le_div_iff₀ hc).mpr
  nlinarith

end Probability

theorem quota_one (p : ℕ → ℚ) (T : ℕ) : quotaLower 1 p T 0 = 1 - (1 - p 0) ^ T := by
  induction T with
  | zero => simp [quotaLower]
  | succ T ih =>
    rw [quotaLower, if_neg (by decide : ¬1 ≤ 0), ih, quota_full 1 p T 1 le_rfl, pow_succ]
    ring

theorem quota_insufficient (n : ℕ) (p : ℕ → ℚ) (T j : ℕ) (h : T + j < n) :
    quotaLower n p T j = 0 := by
  induction T generalizing j with
  | zero => simp [quotaLower, show ¬n ≤ j by omega]
  | succ T ih =>
    rw [quotaLower, if_neg (by omega), ih j (by omega), ih (j + 1) (by omega)]
    ring

section CollectProbability
variable {I V K Seed : Type} [DecidableEq K] [DecidableEq Seed]

def scanCounts (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (schedule : Seed → List I) (i : ℕ) (w : Seed) : ℕ :=
  retainedCount n label key attempt (schedule w) i

omit [DecidableEq Seed] in
theorem scan_count_laws (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (hc : KeyCoherent label key attempt)
    (D : Finset Seed) (schedule : Seed → List I) (T : ℕ) :
    CountLaws D (scanCounts n label key attempt schedule) n T :=
  ⟨fun _ _ => retained_zero n label key attempt _,
    fun i _ w _ => retained_le n label key attempt hc (schedule w) i,
    fun i _ w _ => retained_step n label key attempt (schedule w) i⟩

/-- Probability of actual collect success, including retries and duplicates. -/
theorem collect_probability_lower (n : ℕ) (label : I → K) (key : V → K)
    (attempt : I → Attempt V) (hc : KeyCoherent label key attempt)
    (D : Finset Seed) (hD : D.Nonempty) (schedule : Seed → List I) (T : ℕ)
    (hlen : ∀ w ∈ D, (schedule w).length = T) (p : ℕ → ℚ)
    (hp : ProgressBounds D (scanCounts n label key attempt schedule) n T p) :
    quotaLower n p T 0 ≤ Prob.probability D
      (D.filter fun w => (collect n label key attempt (schedule w)).value.isSome) := by
  have h := quota_probability_lower D hD _ n T p
    (scan_count_laws n label key attempt hc D schedule T) hp
  have he : D.filter (fun w => scanCounts n label key attempt schedule T w = n) =
      D.filter (fun w => (collect n label key attempt (schedule w)).value.isSome) := by
    apply Finset.filter_congr
    intro w hw
    rw [collect_success_iff_quota n label key attempt hc, hlen w hw]
    rfl
  rw [he] at h
  exact h
end CollectProbability

section Acquisition
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
variable {q : ℕ} [Fact q.Prime] {A : Type} [AddCommGroup A] [Module (ZMod q) A]
  [DecidableEq A] {Ω S : Type} {k : ℕ}

/-- Named view of the existing inner candidate lambda, not another collector. -/
def roundAttempt (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A)
    (pr : (ZMod q)ˣ × IPASchedule q k) :
    Attempt (Σ x : (ZMod q)ˣ, Σ ob : Observation m s (.inner k x),
      AcquiredTree m ob.after ob.packet (child_statement st lr x)) :=
  match query m (restore m ⟨s, hs⟩) (.inner k pr.1) with
  | none => ⟨none, [.query, .rejected .adversaryAbort]⟩
  | some o =>
    let a := acquireTree m o.after (o.reachable hs) o.packet
      (child_statement st lr pr.1) pr.2
    ⟨a.value.map (fun t => ⟨pr.1, o, t⟩), .query :: a.trace⟩

theorem round_key_coherent (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A) :
    KeyCoherent (fun pr => (pr.1 : ZMod q) ^ 2) (fun v => (v.1 : ZMod q) ^ 2)
      (roundAttempt m s hs st lr) := by
  intro pr v hv
  unfold roundAttempt at hv
  split at hv
  · simp at hv
  · dsimp only at hv
    obtain ⟨tr, _, he⟩ := Option.map_eq_some_iff.mp hv
    subst v
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem tree_collect_event (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A)
    (ps : IPASchedule q (k + 1)) :
    (acquireTree m s hs (.round lr) st ps).value.isSome =
      (collect 4 (fun pr => (pr.1 : ZMod q) ^ 2) (fun v => (v.1 : ZMod q) ^ 2)
        (roundAttempt m s hs st lr) ps).value.isSome := by
  unfold acquireTree
  dsimp -zeta only
  extract_lets candidate out
  have hc : candidate = roundAttempt m s hs st lr := by
    funext pr
    unfold candidate roundAttempt
    split <;> rename_i he <;> simp only [he]
  have hout : out = collect 4 (fun pr => (pr.1 : ZMod q) ^ 2)
      (fun v => (v.1 : ZMod q) ^ 2) (roundAttempt m s hs st lr) ps := by
    dsimp only [out]
    rw [hc]
  split <;> rename_i h <;> rw [← hout, h] <;> rfl

/-- Named view of the existing eta candidate at its concrete post-e snapshot. -/
def etaAttempt (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A)
    (e t : ZMod q) (pr : (ZMod q)ˣ × IPASchedule q k) :
    Attempt (Σ eta : (ZMod q)ˣ, Σ ob : Observation m s (.binding eta),
      AcquiredTree m ob.after ob.packet (P.toIPA (C.responseClaim p ann e t) eta)) :=
  match query m (restore m ⟨s, hs⟩) (.binding pr.1) with
  | none => ⟨none, [.query, .rejected .adversaryAbort]⟩
  | some o =>
    let a := acquireTree m o.after (o.reachable hs) o.packet
      (P.toIPA (C.responseClaim p ann e t) pr.1) pr.2
    ⟨a.value.map (fun tr => ⟨pr.1, o, tr⟩), .query :: a.trace⟩

theorem eta_key_coherent (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) (e t : ZMod q) :
    KeyCoherent Prod.fst (fun v => v.1) (etaAttempt p m s hs ann e t) := by
  intro pr v hv
  unfold etaAttempt at hv
  split at hv
  · simp at hv
  · dsimp only at hv
    obtain ⟨tr, _, he⟩ := Option.map_eq_some_iff.mp hv
    subst v
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem node_collect_event (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) (e t z : ZMod q)
    (o : Observation m s (.outer e)) (ho : query m s (.outer e) = some o)
    (ha : o.packet = .scalar t z) (hv : C.scalarCheck p ann e t z) (ps : EtaSchedule q k) :
    (acquireNode p m s hs ann e ps).value.isSome =
      (collect 2 Prod.fst (fun v => v.1)
        (etaAttempt p m o.after (o.reachable hs) ann e t) ps).value.isSome := by
  unfold acquireNode
  simp (config := { zeta := false }) only [ho]
  split
  · rename_i t' z' ha'
    obtain ⟨ht,hz⟩ := Packet.scalar.inj (ha'.symm.trans ha)
    subst t'; subst z'
    simp (config := { zeta := false }) only [dif_pos hv]
    extract_lets candidate out
    have hc : candidate = etaAttempt p m o.after (o.reachable hs) ann e t := by
      funext pr
      unfold candidate etaAttempt
      split <;> rename_i he <;> simp only [he]
    have hout : out = collect 2 Prod.fst (fun v => v.1)
        (etaAttempt p m o.after (o.reachable hs) ann e t) ps := by
      dsimp only [out]
      rw [hc]
    split <;> rename_i he <;> rw [← hout, he] <;> rfl
  · rename_i hbad
    exact False.elim (hbad t z ha)

theorem outer_key_coherent (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) :
    KeyCoherent Prod.fst (fun v => v.val.challenge)
      (fun pr => acquireNode p m s hs ann pr.1 pr.2) := by
  intro pr v hv
  dsimp only at hv
  unfold acquireNode at hv
  split at hv
  · simp at hv
  · split at hv
    · split at hv
      · dsimp only at hv
        split at hv
        · simp at hv
        · cases hv; rfl
      · simp at hv
    · simp at hv

theorem acquisition_collect_event (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (o : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (ho : query m (initialSnapshot m) .commit = some o) (ha : o.packet = .announcement ann)
    (ps : ProbeSchedule q k) :
    (acquireCompressedFork p m ps).outcome.isOk =
      (collect 3 Prod.fst (fun v => v.val.challenge)
        (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2)
        ps).value.isSome := by
  unfold acquireCompressedFork acquireCertified
  simp only [ho]
  split
  · rename_i ann' ha'
    have h : ann' = ann := Packet.announcement.inj (ha'.symm.trans ha)
    subst ann'
    split <;> rename_i he <;> simp [he, Except.map, Except.isOk, Except.toBool]
  · rename_i hbad
    exact False.elim (hbad ann ha)

variable {Seed : Type} [DecidableEq Seed]

theorem tree_progress_probability_lower (m : AdversaryModel q A Ω S) (s : Snapshot q S)
    (hs : ReachableSnapshot m s) (st : Statement q A (k + 1)) (lr : RoundMessages A)
    (D : Finset Seed) (hD : D.Nonempty) (schedule : Seed → IPASchedule q (k + 1))
    (T : ℕ) (hlen : ∀ w ∈ D, (schedule w).length = T) (p : ℕ → ℚ)
    (hp : ProgressBounds D (scanCounts 4 (fun pr => (pr.1 : ZMod q) ^ 2)
      (fun v => (v.1 : ZMod q) ^ 2) (roundAttempt m s hs st lr) schedule) 4 T p) :
    quotaLower 4 p T 0 ≤ Prob.probability D
      (D.filter fun w => (acquireTree m s hs (.round lr) st (schedule w)).value.isSome) := by
  simp_rw [tree_collect_event]
  exact collect_probability_lower 4 _ _ _ (round_key_coherent m s hs st lr)
    D hD schedule T hlen p hp

theorem node_progress_probability_lower (claim : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (s : Snapshot q S) (hs : ReachableSnapshot m s) (ann : F.Announcement A) (e t z : ZMod q)
    (o : Observation m s (.outer e)) (ho : query m s (.outer e) = some o)
    (ha : o.packet = .scalar t z) (hv : C.scalarCheck claim ann e t z)
    (D : Finset Seed) (hD : D.Nonempty) (schedule : Seed → EtaSchedule q k)
    (T : ℕ) (hlen : ∀ w ∈ D, (schedule w).length = T) (p : ℕ → ℚ)
    (hp : ProgressBounds D (scanCounts 2 Prod.fst (fun v => v.1)
      (etaAttempt claim m o.after (o.reachable hs) ann e t) schedule) 2 T p) :
    quotaLower 2 p T 0 ≤ Prob.probability D
      (D.filter fun w => (acquireNode claim m s hs ann e (schedule w)).value.isSome) := by
  simp_rw [node_collect_event claim m s hs ann e t z o ho ha hv]
  exact collect_probability_lower 2 _ _ _
    (eta_key_coherent claim m o.after (o.reachable hs) ann e t) D hD schedule T hlen p hp

theorem acquisition_progress_probability_lower (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (o : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (ho : query m (initialSnapshot m) .commit = some o) (ha : o.packet = .announcement ann)
    (D : Finset Seed) (hD : D.Nonempty) (schedule : Seed → ProbeSchedule q k)
    (T : ℕ) (hlen : ∀ w ∈ D, (schedule w).length = T) (rates : ℕ → ℚ)
    (hp : ProgressBounds D (scanCounts 3 Prod.fst (fun v => v.val.challenge)
      (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2)
      schedule) 3 T rates) :
    quotaLower 3 rates T 0 ≤ Prob.probability D
      (D.filter fun w => (acquireCompressedFork p m (schedule w)).outcome.isOk) := by
  simp_rw [acquisition_collect_event p m o ann ho ha]
  exact collect_probability_lower 3 _ _ _
    (outer_key_coherent p m o.after (o.reachable .initial) ann)
    D hD schedule T hlen rates hp

/-- A positive quota bound gives an actual model-provenanced extraction. -/
theorem positive_progress_extracts (p : F.Claim q A k) (m : AdversaryModel q A Ω S)
    (o : Observation m (initialSnapshot m) .commit) (ann : F.Announcement A)
    (ho : query m (initialSnapshot m) .commit = some o) (ha : o.packet = .announcement ann)
    (D : Finset Seed) (hD : D.Nonempty) (schedule : Seed → ProbeSchedule q k)
    (T : ℕ) (hlen : ∀ w ∈ D, (schedule w).length = T) (rates : ℕ → ℚ)
    (hp : ProgressBounds D (scanCounts 3 Prod.fst (fun v => v.val.challenge)
      (fun pr => acquireNode p m o.after (o.reachable .initial) ann pr.1 pr.2) schedule) 3 T rates)
    (hpos : 0 < quotaLower 3 rates T 0) :
    ∃ w ∈ D, ∃ f, (acquireCompressedFork p m (schedule w)).outcome = .ok f ∧
      ForkProvenance m f ∧ F.ResultValid p (C.extractCompressed p f) :=
  positive_schedule_probability_extracts p m D schedule
    (hpos.trans_le (acquisition_progress_probability_lower p m o ann ho ha D hD
      schedule T hlen rates hp))
end Acquisition

/-- Removing already retained classes loses at most their probability mass.
The child success event and blocked event must refer to the same conditional
finite experiment; this does not infer child density from leaf acceptance. -/
theorem unblocked_probability_lower {Seed : Type} [DecidableEq Seed]
    (D S B : Finset Seed) (hD : D.Nonempty) (hS : S ⊆ D) (hB : B ⊆ D)
    (d blocked : ℚ) (hd : d ≤ Prob.probability D S)
    (hb : Prob.probability D B ≤ blocked) :
    max 0 (d - blocked) ≤ Prob.probability D (S \ B) := by
  have hc : (0 : ℚ) < D.card := by exact_mod_cast hD.card_pos
  have hi : ((S ∩ B).card : ℚ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have he : ((S \ B).card : ℚ) + (S ∩ B).card = S.card := by
    exact_mod_cast Finset.card_sdiff_add_card_inter S B
  have hsub : S \ B ⊆ D := Finset.Subset.trans Finset.sdiff_subset hS
  have hnon := CryptoBulletproofsIPATreeProbabilityContract.probability_nonnegative D (S \ B)
  apply max_le hnon
  unfold Prob.probability at *
  rw [Finset.inter_eq_left.mpr hS] at hd
  rw [Finset.inter_eq_left.mpr hB] at hb
  rw [Finset.inter_eq_left.mpr hsub]
  have hd' := (le_div_iff₀ hc).mp hd
  have hb' := (div_le_iff₀ hc).mp hb
  apply (le_div_iff₀ hc).mpr
  nlinarith

structure CryptoHiddenScalarForkProgressProbabilityContractSuite : Prop where
  quota_bound : ∀ (Seed : Type) [DecidableEq Seed] (D : Finset Seed), D.Nonempty →
    ∀ (N : ℕ → Seed → ℕ) (n T : ℕ) (p : ℕ → ℚ),
    CountLaws D N n T → ProgressBounds D N n T p →
    quotaLower n p T 0 ≤ Prob.probability D (D.filter fun w => N T w = n)
  collector_bound : ∀ (I V K Seed : Type) [DecidableEq K] [DecidableEq Seed]
    (n : ℕ) (label : I → K) (key : V → K) (attempt : I → Attempt V),
    KeyCoherent label key attempt → ∀ (D : Finset Seed), D.Nonempty →
    ∀ (schedule : Seed → List I) (T : ℕ), (∀ w ∈ D, (schedule w).length = T) →
    ∀ p, ProgressBounds D (scanCounts n label key attempt schedule) n T p →
    quotaLower n p T 0 ≤ Prob.probability D
      (D.filter fun w => (collect n label key attempt (schedule w)).value.isSome)
  first_success : ∀ p T, quotaLower 1 p T 0 = 1 - (1 - p 0) ^ T
  removal : ∀ (Seed : Type) [DecidableEq Seed] (D S B : Finset Seed), D.Nonempty →
    S ⊆ D → B ⊆ D → ∀ d blocked, d ≤ Prob.probability D S →
    Prob.probability D B ≤ blocked → max 0 (d - blocked) ≤ Prob.probability D (S \ B)

theorem verification_suite : CryptoHiddenScalarForkProgressProbabilityContractSuite where
  quota_bound := fun _ _ => quota_probability_lower
  collector_bound := fun _ _ _ _ _ _ => collect_probability_lower
  first_success := quota_one
  removal := fun _ _ => unblocked_probability_lower
end CryptoHiddenScalarForkProgressProbabilityContract

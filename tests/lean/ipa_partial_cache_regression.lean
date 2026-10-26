/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAPartialBranchCacheResourceContract

namespace IPAPartialCacheRegression
open scoped BigOperators
open CryptoBulletproofsIPAPartialBranchCacheResourceContract
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
open CryptoBulletproofsIPATreeProbabilityContract (probability)
open CryptoBulletproofsIPARecursiveTreeGeneratorContract (Source leafCount)
namespace NR
export CryptoBulletproofsIPAMultiLevelNodeRetryGeneratorContract (generate Tape)
end NR
set_option maxRecDepth 50000

-- Independent fixed tables: no complete row, but every column eventually succeeds.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def left : Cache ℕ := ![some 10, some 20, none, none]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def right : Cache ℕ := ![none, none, some 30, some 40]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def full : Cache ℕ := ![some 11, some 21, some 31, some 41]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def allBad : Cache ℕ := emptyCache
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def complement : List (Cache ℕ) := [left, right]

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache complement).2 = 6 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runReset complement).2 = 8 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : complete (runCache emptyCache complement).1 = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : complete (runReset complement).1 = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache complement).1 = ![some 10, some 20, some 30, some 40] :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache complement).2 < (runReset complement).2 :=
  strict_saving_after_partial left right [] (by decide +kernel) 0 (by decide +kernel)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache ([] : List (Cache ℕ))).2 = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runReset ([] : List (Cache ℕ))).2 = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : complete (runCache emptyCache ([] : List (Cache ℕ))).1 = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache [left]).2 = (runReset [left]).2 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache [left]).2 = 4 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : complete (runCache emptyCache [left]).1 = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache [allBad, allBad]).2 = 8 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache [allBad, allBad]).2 = (runReset [allBad, allBad]).2 :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache [full, allBad, allBad]).2 = 4 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runReset [full, allBad, allBad]).2 = 4 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache full [allBad, right]).2 = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache left [right]).2 = 2 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : fillMissing left full 0 = some 10 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : fillMissing left full 2 = some 31 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache [left, full]).1 0 = some 10 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runReset [left, full]).1 0 = some 11 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (missing left).card = 2 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (c : Cache ℕ) rows : (runCache c rows).2 ≤ (runReset rows).2 :=
  cache_cost_le_reset c rows
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (rows : List (Cache ℕ)) (h : complete (runReset rows).1 = true) :
    complete (runCache emptyCache rows).1 = true := reset_success_implies_cache _ rows h

-- Exactly 256 equiprobable independent 2-by-4 Boolean tables.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def tables : Finset (Fin 2 → Fin 4 → Bool) := Finset.univ
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def row (w : Fin 4 → Bool) : Cache ℕ := fun j => if w j then some j.val else none
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def rows (w : Fin 2 → Fin 4 → Bool) : List (Cache ℕ) := [row (w 0), row (w 1)]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def cachedGood := tables.filter (fun w => complete (runCache emptyCache (rows w)).1)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def resetGood := tables.filter (fun w => complete (runReset (rows w)).1)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def expectedCacheCalls : ℚ := (∑ w ∈ tables, ((runCache emptyCache (rows w)).2 : ℚ)) / tables.card
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def expectedResetCalls : ℚ := (∑ w ∈ tables, ((runReset (rows w)).2 : ℚ)) / tables.card

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : tables.card = 256 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : cachedGood.card = 81 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : resetGood.card = 31 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability tables cachedGood = 81/256 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : probability tables resetGood = 31/256 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1 - (1 - (1/2 : ℚ))^2)^4 = 81/256 := by norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : 1 - (1 - (1/2 : ℚ)^4)^2 = 31/256 := by norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (31/256 : ℚ) < 81/256 := by norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : expectedCacheCalls = 6 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : expectedResetCalls = 31/4 := by decide +kernel

-- The full computed child Statement can coincide for DISTINCT challenge scalars.
-- This is an algebraic fixture, not an assumption of independent generators.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def s (k : ℕ) : Statement 101 (ZMod 101) k := ⟨1, fun _ => 0, fun _ => 0, 0⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def msg : RoundMessages (ZMod 101) := ⟨0, 0⟩
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def calls : Fin 4 → ZMod 101 := ![1, 2, 3, 4]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def units := CryptoBulletproofsWitnessExtraction.Examples.units
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def fork (k : ℕ) : FixedFork 101 (ZMod 101) k where
  parent := s (k + 1)
  msg := msg
  u := units
  distinct := by decide +kernel

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def src : Source 101 (ZMod 101) Bool where
  leaf c w := if w then some (c, 0, 0) else none
  node _ c _ := some (c, msg, calls)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongContext : Source 101 (ZMod 101) Bool :=
  { src with leaf := fun c _ => some ({ c with P := c.P + 1 }, 0, 0) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongScalar : Source 101 (ZMod 101) Bool :=
  { src with leaf := fun c _ => some (c, 1, 1) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def two (_ : ℕ) : ℕ := 2
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def leafRows : List (Fin 4 → NR.Tape two Bool 0) :=
  [![true, true, false, false], ![false, false, true, true]]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def recursiveGood : NR.Tape two Bool 1 := fun _ => (true, fun _ => true)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def recursiveBad : NR.Tape two Bool 1 := fun _ => (true, fun _ => false)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def recursiveRows : List (Fin 4 → NR.Tape two Bool 1) :=
  [![recursiveGood, recursiveGood, recursiveBad, recursiveBad],
   ![recursiveBad, recursiveBad, recursiveGood, recursiveGood]]
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def moved : FixedFork 101 (ZMod 101) 0 := { fork 0 with msg := ⟨1, 0⟩ }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def leaf : IPATranscriptTree 101 (ZMod 101) 0 := .leaf (childContext (fork 0) 0) 0 0
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def invalidLeaf : IPATranscriptTree 101 (ZMod 101) 0 := .leaf (childContext (fork 0) 0) 1 1

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (units 0 : ZMod 101) ≠ units 1 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : childContext (fork 0) 0 = childContext (fork 0) 1 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : childContext (fork 0) 0 ≠ childContext moved 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ValidAcceptingTree (childContext (fork 0) 0) leaf := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ ValidAcceptingTree (childContext moved 0) leaf := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ¬ ValidAcceptingTree (childContext (fork 0) 0) invalidLeaf := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedTransfer (childContext (fork 0) 0) (childContext (fork 0) 1) leaf).isSome =
    true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedTransfer (childContext (fork 0) 0) (childContext moved 0) leaf).isSome =
    false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (new : Statement 101 (ZMod 101) 0) :
    ValidAcceptingTree new leaf ↔ new = childContext (fork 0) 0 :=
  valid_tree_transfer_iff (childContext (fork 0) 0) new leaf (by decide +kernel)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedTransfer (childContext (fork 0) 0) (childContext (fork 0) 0)
    invalidLeaf).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (NR.generate two src (childContext (fork 0) 0) true).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (NR.generate two src (childContext (fork 0) 0) false).isSome = false :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (cachedGenerate (fork 0) two src leafRows).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : complete (runReset (childRows (fork 0) two src leafRows)).1 = false :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache (childRows (fork 0) two src leafRows)).2 = 6 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runReset (childRows (fork 0) two src leafRows)).2 = 8 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((cachedGenerate (fork 0) two src leafRows).map leafCount) = some 4 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (cachedGenerate (fork 1) two src recursiveRows).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : ((cachedGenerate (fork 1) two src recursiveRows).map leafCount) = some 16 :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (runCache emptyCache (childRows (fork 1) two src recursiveRows)).2 = 6 :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (cachedGenerate moved two src leafRows).isSome = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (cachedGenerate (fork 0) two wrongContext leafRows).isSome = false :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (cachedGenerate (fork 0) two wrongScalar leafRows).isSome = false := by decide +kernel

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def checkedCached (k : ℕ) (tapes : List (Fin 4 → NR.Tape two Bool k)) : Bool :=
  match cachedGenerate (fork k) two src tapes with
  | none => false
  | some t => (checked_extract (s (k + 1)) t).isOk
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedCached 0 leafRows = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : checkedCached 1 recursiveRows = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (t : IPATranscriptTree 101 (ZMod 101) 1)
    (h : cachedGenerate (fork 0) two src leafRows = some t) : ValidAcceptingTree (s 1) t :=
  cachedGenerate_valid (fork 0) two src leafRows t h

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (cacheTrace (emptyCache : Cache ℕ) complement).length = 6 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (resetTrace complement).length = 8 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1, (0 : Fin 4)) ∉ cacheTrace (emptyCache : Cache ℕ) complement := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1, (2 : Fin 4)) ∈ cacheTrace (emptyCache : Cache ℕ) complement := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (1, (0 : Fin 4)) ∈ resetTrace complement := by decide +kernel

open CryptoBulletproofsIPAProductTapeCandidateGeneratorContract (singleProbability goodTapes)
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def coins : Fin 4 → Finset Bool := fun _ => Finset.univ
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def accepts (_ : Fin 4) : Bool → Bool := id
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : singleProbability (branchSpace coins 2) (cacheEvent 2 accepts) = 81/256 := by
  rw [cache_probability_exact coins
    (by intro j; change (Finset.univ : Finset Bool).Nonempty; decide +kernel)]
  have h : ∀ j, singleProbability (coins j) (accepts j) = 1/2 := by
    intro j; change singleProbability (Finset.univ : Finset Bool) id = 1/2; decide +kernel
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : singleProbability (branchSpace coins 2) (resetEvent 2 accepts) = 31/256 := by
  rw [reset_probability_exact coins
    (by intro j; change (Finset.univ : Finset Bool).Nonempty; decide +kernel)]
  have h : ∀ j, singleProbability (coins j) (accepts j) = 1/2 := by
    intro j; change singleProbability (Finset.univ : Finset Bool) id = 1/2; decide +kernel
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

-- The exact finite-product law also applies to the ACTUAL child generator.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : singleProbability (branchSpace coins 2)
    (fun w => (cachedGenerate (fork 0) two src
      (List.ofFn (fun r j => w j r))).isSome) = 81/256 := by
  let C : Fin 4 → Finset (NR.Tape two Bool 0) := coins
  have hp := cachedGenerate_probability_exact (fork 0) two src C
    (by intro j; change (Finset.univ : Finset Bool).Nonempty; decide +kernel) 2
  have h : ∀ j, singleProbability (C j)
      (fun ω => (NR.generate two src (childContext (fork 0) j) ω).isSome) = 1/2 := by
    intro j; fin_cases j <;> decide +kernel
  have rhs : (∏ j, (1 - (1 - singleProbability (C j)
      (fun ω => (NR.generate two src (childContext (fork 0) j) ω).isSome))^2)) = 81/256 := by
    simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  exact hp.trans rhs

-- Structural assembly does NOT certify arbitrary externally supplied cached values.
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def poisoned : Cache (IPATranscriptTree 101 (ZMod 101) 0) := fun _ => some invalidLeaf
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def stale : Cache (IPATranscriptTree 101 (ZMod 101) 0) := fun _ => some leaf
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def assemblyChecks (F : FixedFork 101 (ZMod 101) 0)
    (c : Cache (IPATranscriptTree 101 (ZMod 101) 0)) : Bool :=
  match assemble F c with
  | none => false
  | some t => (checked_extract F.parent t).isOk
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (assemble (fork 0) poisoned).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : assemblyChecks (fork 0) poisoned = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (assemble moved stale).isSome = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : assemblyChecks moved stale = false := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : assemblyChecks (fork 0) stale = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example (t : IPATranscriptTree 101 (ZMod 101) 1)
    (h : cachedGenerate (fork 0) two src leafRows = some t) :
    checked_extract (s 1) t = .ok (extractTree t) ∧ ResultValid (s 1) (extractTree t) :=
  cachedGenerate_extracts (fork 0) two src leafRows t h

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def wrongHeader : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ c _ => some ({ c with P := c.P + 1 }, msg, calls) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def zeroHeader : Source 101 (ZMod 101) Bool :=
  { src with node := fun _ c _ => some (c, msg, ![0, 2, 3, 4]) }
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedCachedNode two wrongHeader (s 1) true leafRows).2 = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedCachedNode two wrongHeader (s 1) true leafRows).1.isSome = false :=
  by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedCachedNode two zeroHeader (s 1) true leafRows).2 = 0 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedCachedNode two src (s 1) true leafRows).2 = 6 := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
example : (checkedCachedNode two src (s 1) true leafRows).1.isSome = true := by decide +kernel

end IPAPartialCacheRegression
open IPAPartialCacheRegression CryptoBulletproofsIPAPartialBranchCacheResourceContract

set_option maxHeartbeats 8000000 in
-- Kernel reduction of fixed fixtures retains the original heartbeat budget.
def main : IO Unit := do
  let checks : List Bool := [
    decide ((runCache emptyCache complement).2 = 6),
    decide ((runReset complement).2 = 8),
    complete (runCache emptyCache complement).1,
    !(complete (runReset complement).1),
    decide ((runCache emptyCache [left]).2 = (runReset [left]).2),
    decide ((runCache emptyCache ([] : List (Cache ℕ))).2 = 0),
    decide ((runCache full [left, right]).2 = 0),
    decide ((runCache emptyCache [allBad, allBad]).2 = 8),
    decide (fillMissing left full 0 = some 10),
    decide (fillMissing left full 2 = some 31),
    decide (cachedGood.card = 81),
    decide (resetGood.card = 31),
    decide (expectedCacheCalls = 6),
    decide (expectedResetCalls = 31/4),
    decide (childContext (fork 0) 0 = childContext (fork 0) 1),
    !(checkedTransfer (childContext (fork 0) 0) (childContext moved 0) leaf).isSome,
    (cachedGenerate (fork 0) two src leafRows).isSome,
    (cachedGenerate (fork 1) two src recursiveRows).isSome,
    !(cachedGenerate moved two src leafRows).isSome,
    !(cachedGenerate (fork 0) two wrongContext leafRows).isSome,
    !(cachedGenerate (fork 0) two wrongScalar leafRows).isSome,
    checkedCached 0 leafRows,
    checkedCached 1 recursiveRows,
    decide ((runCache emptyCache (childRows (fork 1) two src recursiveRows)).2 = 6),
    decide ((cacheTrace (emptyCache : Cache ℕ) complement).length = 6),
    decide ((1, (0 : Fin 4)) ∉ cacheTrace (emptyCache : Cache ℕ) complement),
    !(assemblyChecks (fork 0) poisoned),
    !(assemblyChecks moved stale),
    decide ((checkedCachedNode two wrongHeader (s 1) true leafRows).2 = 0),
    decide ((checkedCachedNode two src (s 1) true leafRows).2 = 6)]
  unless checks.all id do throw (IO.userError "partial IPA cache regression failed")
  IO.println s!"IPA_PARTIAL_CACHE_OK {checks.length}"

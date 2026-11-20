/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Lean.Elab.Tactic.Omega

/-! Numerical model of shrincs_sf_leaf_select, SHRINCS/shrincs-bip
ad93be730f0a774631b4e8aac9905f0071b1276b. Shape codes 0 and 1
denote unbalanced and balanced. Coordinates are (index, height).
The input encoding bounds depth to a byte and the present counter to UInt64.
-/
namespace ShrincsLeaf

def select (shape depth : Nat) (counter : Option Nat) : Option (Nat × Nat) := do
  let c ← counter
  if depth = 0 then none
  else if shape = 0 then
    if c = depth then some (0, 255 - depth)
    else if c < depth then some (1, 254 - c)
    else none
  else if shape = 1 ∧ c < 2 ^ depth then some (c, 255 - depth)
  else none

private theorem decode {shape depth c : Nat} (hd : depth ≤ 255)
    {p : Nat × Nat} (h : select shape depth (some c) = some p) :
    c = (if shape = 0 then (if p.1 = 0 then depth else 254 - p.2) else p.1) := by
  by_cases zero : depth = 0
  · simp [select, zero] at h
  by_cases unbalanced : shape = 0
  · by_cases last : c = depth
    · simp [select, zero, unbalanced, last] at h
      subst p
      simp [unbalanced, last]
    · by_cases live : c < depth
      · simp [select, zero, unbalanced, last, live] at h
        subst p
        simp [unbalanced]
        omega
      · simp [select, zero, unbalanced, last, live] at h
  · by_cases live : shape = 1 ∧ c < 2 ^ depth
    · simp [select, zero, live] at h
      subst p
      simp [unbalanced]
    · simp [select, zero, unbalanced, live] at h

theorem injective_on_success {shape depth a b : Nat} (hd : depth ≤ 255)
    {p : Nat × Nat} (ha : select shape depth (some a) = some p)
    (hb : select shape depth (some b) = some p) : a = b :=
  (decode hd ha).trans (decode hd hb).symm

end ShrincsLeaf

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

namespace QuantumPauliMatrix
structure GI where
  re : Int
  im : Int
  deriving DecidableEq, Repr
def gz : GI := ⟨0,0⟩
def go : GI := ⟨1,0⟩
def ga (a b : GI) : GI := ⟨a.re+b.re,a.im+b.im⟩
def gm (a b : GI) : GI := ⟨a.re*b.re-a.im*b.im,a.re*b.im+a.im*b.re⟩
theorem ga_assoc (a b c : GI) : ga (ga a b) c = ga a (ga b c) := by
  cases a; cases b; cases c; simp [ga, Int.add_assoc]
theorem ga_comm (a b : GI) : ga a b = ga b a := by
  cases a; cases b; simp [ga, Int.add_comm]
theorem gm_assoc (a b c : GI) : gm (gm a b) c = gm a (gm b c) := by
  cases a; cases b; cases c; simp only [gm, GI.mk.injEq]; constructor <;> grind
theorem gm_comm (a b : GI) : gm a b = gm b a := by
  cases a; cases b; simp only [gm, GI.mk.injEq]; constructor <;> grind
theorem gm_add (a b c : GI) : gm a (ga b c) = ga (gm a b) (gm a c) := by
  cases a; cases b; cases c; simp only [gm, ga, GI.mk.injEq]; constructor <;> grind
theorem gm_zero (a : GI) : gm a gz = gz := by cases a; simp [gm,gz]
theorem gm_one (a : GI) : gm a go = a := by cases a; simp [gm,go]
def Basis : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Basis n
abbrev Mat (n : Nat) := Basis n → Basis n → GI
def sumBasis : (n : Nat) → (Basis n → GI) → GI
  | 0, f => f ()
  | n+1, f => ga (sumBasis n (fun j => f (false,j))) (sumBasis n (fun j => f (true,j)))
def mm {n : Nat} (a b : Mat n) : Mat n := fun i k => sumBasis n (fun j => gm (a i j) (b j k))
def ms {n : Nat} (c : GI) (a : Mat n) : Mat n := fun i j => gm c (a i j)
def mt {n : Nat} (a : Mat 1) (b : Mat n) : Mat (n+1) :=
  fun i j => gm (a (i.1,()) (j.1,())) (b i.2 j.2)
theorem sum_scale (n : Nat) (c : GI) (f : Basis n → GI) :
    sumBasis n (fun i => gm c (f i)) = gm c (sumBasis n f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBasis, ih, gm_add]
theorem four_mul (a b c d : GI) : gm (gm a b) (gm c d) = gm (gm a c) (gm b d) := by
  rw [gm_assoc, ← gm_assoc b, gm_comm b c, gm_assoc c, ← gm_assoc]
theorem sum_tensor_term (n : Nat) (a c : GI) (b d : Basis n → GI) :
    sumBasis n (fun j => gm (gm a (b j)) (gm c (d j))) =
    gm (gm a c) (sumBasis n (fun j => gm (b j) (d j))) := by
  calc
    _ = sumBasis n (fun j => gm (gm a c) (gm (b j) (d j))) :=
      congrArg (sumBasis n) (funext (fun j => four_mul a (b j) c (d j)))
    _ = _ := sum_scale n (gm a c) _
theorem tensor_mul {n : Nat} (a c : Mat 1) (b d : Mat n) :
    mm (mt a b) (mt c d) = mt (mm a c) (mm b d) := by
  funext i j
  simp only [mm, mt, sumBasis]
  rw [sum_tensor_term, sum_tensor_term]
  rw [gm_comm (ga _ _), gm_add]
  rw [gm_comm (sumBasis _ _) _, gm_comm (sumBasis _ _) _]
theorem scale_mul {n : Nat} (a b : Mat n) (c d : GI) :
    mm (ms c a) (ms d b) = ms (gm c d) (mm a b) := by
  funext i j
  exact sum_tensor_term n c d _ _
theorem tensor_scales {n : Nat} (a : Mat 1) (b : Mat n) (c d : GI) :
    mt (ms c a) (ms d b) = ms (gm c d) (mt a b) := by
  funext i j
  exact four_mul c _ d _
theorem scale_scale {n : Nat} (a : Mat n) (c d : GI) :
    ms c (ms d a) = ms (gm c d) a := by
  funext i j
  exact (gm_assoc c d _).symm
inductive Phase where
  | one | imag | minusOne | minusImag
  deriving DecidableEq, Repr
open Phase
def phaseNat : Phase → Nat
  | one => 0 | imag => 1 | minusOne => 2 | minusImag => 3
def phaseOfNat (n : Nat) : Phase :=
  match n % 4 with
  | 0 => one | 1 => imag | 2 => minusOne | _ => minusImag
def phaseMul (a b : Phase) : Phase := phaseOfNat (phaseNat a + phaseNat b)
def phaseValue : Phase → GI
  | one => go | imag => ⟨0,1⟩ | minusOne => ⟨-1,0⟩ | minusImag => ⟨0,-1⟩
theorem phase_one_value : phaseValue one = go := rfl
theorem phase_mul_sound (a b : Phase) : phaseValue (phaseMul a b) = gm (phaseValue a) (phaseValue b) := by
  cases a <;> cases b <;> rfl
inductive Axis where
  | identity | x | y | z
  deriving DecidableEq, Repr
open Axis
def axX : Axis → Bool | identity => false | x => true | y => true | z => false
def axZ : Axis → Bool | identity => false | x => false | y => true | z => true
def axisOfBits : Bool → Bool → Axis
  | false,false => identity | true,false => x | true,true => y | false,true => z
def axisMul (a b : Axis) : Axis := axisOfBits (xor (axX a) (axX b)) (xor (axZ a) (axZ b))
def axisPhase : Axis → Axis → Phase
  | identity, _ => one | _, identity => one
  | x,x => one | y,y => one | z,z => one
  | x,y => imag | y,z => imag | z,x => imag
  | y,x => minusImag | z,y => minusImag | x,z => minusImag
def axisMatrix (a : Axis) : Mat 1 := fun i j =>
  match a, i.1, j.1 with
  | identity,false,false | identity,true,true | x,false,true | x,true,false | z,false,false => go
  | z,true,true => ⟨-1,0⟩
  | y,false,true => ⟨0,-1⟩
  | y,true,false => ⟨0,1⟩
  | _,_,_ => gz
theorem axis_mul_sound (a b : Axis) :
    mm (axisMatrix a) (axisMatrix b) = ms (phaseValue (axisPhase a b)) (axisMatrix (axisMul a b)) := by
  cases a <;> cases b <;> funext i j <;>
    rcases i with ⟨i,⟨⟩⟩ <;> rcases j with ⟨j,⟨⟩⟩ <;> cases i <;> cases j <;> rfl
structure Pauli4QPhase where
  phase : Phase
  a : Axis
  b : Axis
  c : Axis
  d : Axis
  deriving DecidableEq, Repr
def tailPhase (p q : Pauli4QPhase) : Phase :=
  phaseMul (axisPhase p.a q.a) (phaseMul (axisPhase p.b q.b)
    (phaseMul (axisPhase p.c q.c) (phaseMul (axisPhase p.d q.d) one)))
def mulPauli4Q (p q : Pauli4QPhase) : Pauli4QPhase :=
  { phase := phaseMul (phaseMul p.phase q.phase) (tailPhase p q)
    a := axisMul p.a q.a, b := axisMul p.b q.b
    c := axisMul p.c q.c, d := axisMul p.d q.d }
def scalarIdentity : Mat 0 := fun _ _ => go
def denote4 (p : Pauli4QPhase) : Mat 4 :=
  ms (phaseValue p.phase) (mt (axisMatrix p.a) (mt (axisMatrix p.b)
    (mt (axisMatrix p.c) (mt (axisMatrix p.d) scalarIdentity))))
theorem scalar_identity_mul : mm scalarIdentity scalarIdentity = ms go scalarIdentity := rfl
theorem mulPauli4Q_matrix_sound (p q : Pauli4QPhase) :
    denote4 (mulPauli4Q p q) = mm (denote4 p) (denote4 q) := by
  simp only [denote4, mulPauli4Q, scale_mul, tensor_mul, axis_mul_sound,
    scalar_identity_mul, tensor_scales, scale_scale, tailPhase, phase_mul_sound, phase_one_value]
def cnotMatrix : Mat 2 := fun i j =>
  if i.1 == j.1 && i.2.1 == xor j.1 j.2.1 then go else gz
def denote2 (phase : Phase) (a b : Axis) : Mat 2 :=
  ms (phaseValue phase) (mt (axisMatrix a) (mt (axisMatrix b) scalarIdentity))
def cnotPhase (phase : Phase) (a b : Axis) : Phase :=
  phaseMul phase (if axX a && axZ b && !(xor (axX b) (axZ a)) then minusOne else one)
def cnotControl (a b : Axis) : Axis := axisOfBits (axX a) (xor (axZ a) (axZ b))
def cnotTarget (a b : Axis) : Axis := axisOfBits (xor (axX b) (axX a)) (axZ b)
set_option maxHeartbeats 2000000 in
theorem cnot_matrix_sound (phase : Phase) (a b : Axis) :
    mm (mm cnotMatrix (denote2 phase a b)) cnotMatrix =
    denote2 (cnotPhase phase a b) (cnotControl a b) (cnotTarget a b) := by
  cases phase <;> cases a <;> cases b <;> funext i j <;>
    rcases i with ⟨i0,i1,⟨⟩⟩ <;> rcases j with ⟨j0,j1,⟨⟩⟩ <;>
    cases i0 <;> cases i1 <;> cases j0 <;> cases j1 <;> rfl
structure BoundedBps where
  val : Int
  nonneg : 0 ≤ val
  le_scale : val ≤ 10000
-- Only these bounded interfaces are exposed for the channel.
def channelNumerator (f p : BoundedBps) : Int :=
  (10000 - p.val) * f.val + 2500 * p.val
theorem channel_numerator_bounds (f p : BoundedBps) :
    0 ≤ channelNumerator f p ∧ channelNumerator f p ≤ 100000000 := by
  have hp0 := p.nonneg
  have hp1 := p.le_scale
  have h0 := Int.mul_nonneg (show 0 ≤ 10000 - p.val by omega) f.nonneg
  have h1 := Int.mul_le_mul_of_nonneg_left f.le_scale (show 0 ≤ 10000-p.val by omega)
  simp only [channelNumerator]
  omega
def channelFloor (f p : BoundedBps) : BoundedBps :=
  let k := channelNumerator f p / 10000
  { val := k
    nonneg := by have h := channel_numerator_bounds f p; dsimp [k]; omega
    le_scale := by have h := channel_numerator_bounds f p; dsimp [k]; omega }
theorem channel_rounding_bound (f p : BoundedBps) :
    10000 * (channelFloor f p).val ≤ channelNumerator f p ∧
    channelNumerator f p < 10000 * ((channelFloor f p).val + 1) := by
  simp only [channelFloor]
  omega
def gc (a : GI) : GI := ⟨a.re, -a.im⟩
def adjoint {n : Nat} (a : Mat n) : Mat n := fun i j => gc (a j i)
def identity2 : Mat 2 := fun i j => if i.1 == j.1 && i.2.1 == j.2.1 then go else gz
theorem cnot_self_adjoint : adjoint cnotMatrix = cnotMatrix := by
  funext i j
  rcases i with ⟨i0,i1,⟨⟩⟩; rcases j with ⟨j0,j1,⟨⟩⟩
  cases i0 <;> cases i1 <;> cases j0 <;> cases j1 <;> rfl
theorem cnot_involutive_matrix : mm cnotMatrix cnotMatrix = identity2 := by
  funext i j
  rcases i with ⟨i0,i1,⟨⟩⟩; rcases j with ⟨j0,j1,⟨⟩⟩
  cases i0 <;> cases i1 <;> cases j0 <;> cases j1 <;> rfl
theorem cnot_conjugation_sound (phase : Phase) (a b : Axis) :
    mm (mm cnotMatrix (denote2 phase a b)) (adjoint cnotMatrix) =
    denote2 (cnotPhase phase a b) (cnotControl a b) (cnotTarget a b) := by
  rw [cnot_self_adjoint, cnot_matrix_sound]

def xB : Pauli4QPhase := ⟨one, identity, x, identity, identity⟩
def zB : Pauli4QPhase := ⟨one, identity, z, identity, identity⟩
theorem noncommuting_product_keeps_imaginary_phase :
    mulPauli4Q xB zB = ⟨minusImag, identity, y, identity, identity⟩ ∧
    mulPauli4Q zB xB = ⟨imag, identity, y, identity, identity⟩ := by
  exact ⟨rfl,rfl⟩
theorem channel_zero_noise (f p : BoundedBps) (hp : p.val = 0) :
    (channelFloor f p).val = f.val := by
  simp only [channelFloor, channelNumerator, hp]
  omega
theorem channel_full_noise (f p : BoundedBps) (hp : p.val = 10000) :
    (channelFloor f p).val = 2500 := by
  simp only [channelFloor, channelNumerator, hp]
  omega
/-- Registry contract for the exact, four-phase operator model. -/
structure QuantumPauliMatrixSuite : Prop where
  multiplication : ∀ p q, denote4 (mulPauli4Q p q) = mm (denote4 p) (denote4 q)
  conjugation : ∀ phase a b,
    mm (mm cnotMatrix (denote2 phase a b)) (adjoint cnotMatrix) =
      denote2 (cnotPhase phase a b) (cnotControl a b) (cnotTarget a b)
  rounding : ∀ f p,
    10000 * (channelFloor f p).val ≤ channelNumerator f p ∧
    channelNumerator f p < 10000 * ((channelFloor f p).val + 1)

theorem verification_suite : QuantumPauliMatrixSuite :=
  ⟨mulPauli4Q_matrix_sound, cnot_conjugation_sound, channel_rounding_bound⟩

end QuantumPauliMatrix

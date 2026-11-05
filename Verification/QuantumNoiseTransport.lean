/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCentralDepolarization

/-! Exact transport of a CPTP channel through a unitary prefix. The transported
channel generally differs from the original; equality requires covariance. -/
noncomputable section
namespace QuantumNoiseTransport
open QuantumGateNoiseComposition
open scoped BigOperators ComplexOrder Matrix

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

structure UnitaryGate (n : Type*) [Fintype n] [DecidableEq n] where
  matrix : Matrix n n ℂ
  left : matrix.conjTranspose * matrix = 1
  right : matrix * matrix.conjTranspose = 1

def UnitaryGate.inverse (U : UnitaryGate n) : UnitaryGate n :=
  ⟨U.matrix.conjTranspose, by simpa using U.right, by simpa using U.left⟩

def UnitaryGate.channel (U : UnitaryGate n) : CPTP n Unit :=
  ⟨fun _ => U.matrix, by simpa using U.left⟩

@[simp] theorem unitary_channel_map (U : UnitaryGate n) (M : Matrix n n ℂ) :
    U.channel.map M = U.matrix * M * U.matrix.conjTranspose := by
  simp [CPTP.map, UnitaryGate.channel]

/-- Effective input noise for an error occurring immediately after U. -/
def pullback (U : UnitaryGate n) (E : CPTP n κ) : CPTP n κ where
  op k := U.matrix.conjTranspose * E.op k * U.matrix
  complete := by
    have hk (k : κ) :
        (U.matrix.conjTranspose * E.op k * U.matrix).conjTranspose *
          (U.matrix.conjTranspose * E.op k * U.matrix) =
        U.matrix.conjTranspose * ((E.op k).conjTranspose * E.op k) * U.matrix := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc
        _ = U.matrix.conjTranspose * (E.op k).conjTranspose *
              (U.matrix * U.matrix.conjTranspose) * E.op k * U.matrix := by
                simp only [Matrix.mul_assoc]
        _ = _ := by rw [U.right]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    simp only [hk, ← Matrix.mul_sum, ← Matrix.sum_mul, E.complete, Matrix.mul_one, U.left]

theorem pullback_map (U : UnitaryGate n) (E : CPTP n κ) (M : Matrix n n ℂ) :
    (pullback U E).map M =
      U.matrix.conjTranspose * E.map (U.matrix * M * U.matrix.conjTranspose) * U.matrix := by
  simp only [CPTP.map, pullback, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem slide_channel (U : UnitaryGate n) (E : CPTP n κ) (M : Matrix n n ℂ) :
    E.map (U.matrix * M * U.matrix.conjTranspose) =
      U.matrix * (pullback U E).map M * U.matrix.conjTranspose := by
  rw [pullback_map]
  calc
    _ = (U.matrix * U.matrix.conjTranspose) *
        E.map (U.matrix * M * U.matrix.conjTranspose) *
        (U.matrix * U.matrix.conjTranspose) := by rw [U.right]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

/-- A rectangular branch after a noisy gate has exactly the pulled-back Kraus family. -/
theorem slide_branch {o : Type*} (U : UnitaryGate n) (E : CPTP n κ)
    (L : Matrix o n ℂ) (k : κ) :
    L * E.op k * U.matrix = (L * U.matrix) * (pullback U E).op k := by
  change _ = L * U.matrix * (U.matrix.conjTranspose * E.op k * U.matrix)
  calc
    _ = L * (U.matrix * U.matrix.conjTranspose) * E.op k * U.matrix := by
      rw [U.right, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Covariance is an explicit additional hypothesis, not a property of all CPTP maps. -/
theorem pullback_eq_of_covariant (U : UnitaryGate n) (E : CPTP n κ)
    (hcov : ∀ M, E.map (U.matrix * M * U.matrix.conjTranspose) =
      U.matrix * E.map M * U.matrix.conjTranspose) (M : Matrix n n ℂ) :
    (pullback U E).map M = E.map M := by
  rw [pullback_map, hcov]
  calc
    _ = (U.matrix.conjTranspose * U.matrix) * E.map M *
          (U.matrix.conjTranspose * U.matrix) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [U.left]; simp

open QuantumPauliDensityBridge QuantumBellDiagonalInputs QuantumRectangularSwapping
open QuantumEntanglementSwappingPurificationContract QuantumStateAvailabilityContract
open QuantumCentralDepolarization

def centralGate (U : UnitaryGate PairIndex) : UnitaryGate FourIndex :=
  ⟨embedBC U.matrix,
    by rw [embedBC_adjoint, embedBC_mul, U.left, embedBC_one],
    by rw [embedBC_adjoint, embedBC_mul, U.right, embedBC_one]⟩

theorem central_pullback_operator (U : UnitaryGate PairIndex) (E : CPTP PairIndex κ) (k : κ) :
    (pullback (centralGate U) (centralChannel E)).op k =
      (centralChannel (pullback U E)).op k := by
  simp only [pullback, centralGate, centralChannel, embedBC_adjoint, embedBC_mul]

theorem central_pullback_map (U : UnitaryGate PairIndex) (E : CPTP PairIndex κ)
    (M : FourDensity) :
    (pullback (centralGate U) (centralChannel E)).map M =
      (centralChannel (pullback U E)).map M := by
  simp only [CPTP.map, central_pullback_operator]

/-- Isotropic BC depolarization can be moved through a BC unitary without changing its map. -/
theorem central_depolarizing_transport (U : UnitaryGate PairIndex) (v : Visibility)
    (M : FourDensity) :
    (pullback (centralGate U) (centralChannel (depolarizing v))).map M =
      (centralChannel (depolarizing v)).map M := by
  rw [central_pullback_map]
  ext i j : 2
  rw [central_map, central_map,
    pullback_eq_of_covariant U (depolarizing v)
      (fun N => depolarizing_covariance v U.matrix N U.left U.right)]

structure QuantumNoiseTransportSuite : Prop where
  sliding : ∀ {κ : Type} [Fintype κ] (U : UnitaryGate FourIndex) (E : CPTP FourIndex κ) M,
    E.map (U.matrix * M * U.matrix.conjTranspose) =
      U.matrix * (pullback U E).map M * U.matrix.conjTranspose
  isotropic_transport : ∀ U v M,
    (pullback (centralGate U) (centralChannel (depolarizing v))).map M =
      (centralChannel (depolarizing v)).map M

theorem verification_suite : QuantumNoiseTransportSuite :=
  ⟨slide_channel, central_depolarizing_transport⟩

end QuantumNoiseTransport

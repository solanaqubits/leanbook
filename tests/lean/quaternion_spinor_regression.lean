import Verification.AlgebraQuaternionSpinor
open AlgebraQuaternionSpinor
open scoped Quaternion
noncomputable section

example : basisI * basisJ ≠ basisJ * basisI := by
  intro h
  rw [hamilton_relations.2.2.2.1, hamilton_relations.2.2.2.2.1] at h
  have hk := congrArg (fun q : Quat => q.imK) h
  rw [Quaternion.imK_neg] at hk
  norm_num [basisK] at hk

example (q : Quat) : (q * pureVec (0, 0, 0) * conj q).w = 0 :=
  conjugation_pure q _ rfl

example (q : UnitQuat) : rotate q (0 : Vec3) = 0 := by
  have h := rotate_smul q 0 (0 : Vec3)
  simpa using h

example (v : Vec3) : rotate 1 v = v := rotate_one v
example (q : Quat) (v : Vec3) :
    (-q) * embed v * conj (-q) = q * embed v * conj q := opposite_same_action q _
example (q : UnitQuat) (v : Vec3) : ‖rotate q v‖ = ‖v‖ := rotate_norm q v
example (q : UnitQuat) (u v : Vec3) : dist (rotate q u) (rotate q v) = dist u v :=
  rotate_dist q u v
example (q r : UnitQuat) (v : Vec3) : rotate (q * r) v = rotate q (rotate r v) :=
  rotate_mul q r v
example (q : UnitQuat) (v : Vec3) : rotate q⁻¹ (rotate q v) = v := rotate_inverse q v
example (q : UnitQuat) (v : Vec3) : rotate q (rotate q⁻¹ v) = v := by
  rw [← rotate_mul, mul_inv_cancel, rotate_one]
example : ¬ (∀ q p : Quat, normSq (q * p * conj q) = normSq p) := by
  intro h
  exact nonunit_counterexample (h 2 basisI)
example : Group UnitQuat := inferInstance
example (q : Quat) (h : normSq q = 1) : ((unitOfNormSq q h : UnitQuat) : Quat) = q := rfl

end

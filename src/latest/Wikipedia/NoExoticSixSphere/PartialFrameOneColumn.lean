import Wikipedia.NoExoticSixSphere.PartialFrameColumnFiber

/-!
# One-column frames are the actual unit sphere

Evaluation at a specified unit vector in the one-dimensional source has a
continuous inverse: send a scalar coordinate to that multiple of the target
unit vector. Both spaces carry their original subspace topologies.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.OneColumn

open GLOrthonormalization ColumnCoordinates

local instance sourceDimension : Fact (Module.finrank ℝ (Vector 1) = 0 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable (v : UnitSphere (Vector 1))

theorem scalar_decomposition (z : Vector 1) : inner ℝ v.val z • v.val = z := by
  have h := (split (r := 0) v).symm_apply_apply z
  rw [split_symm_apply, split_fst] at h
  rw [Subsingleton.elim ((split (r := 0) v z).snd) 0, map_zero,
    Submodule.coe_zero, add_zero] at h
  exact h

theorem norm_scalar (z : Vector 1) : ‖inner ℝ v.val z‖ = ‖z‖ := by
  have h := congrArg norm (scalar_decomposition v z)
  simpa only [norm_smul, ClosedHemisphere.unit_norm, mul_one] using h

variable {n : ℕ}

def frame (x : UnitSphere (Vector n)) : Space n 1 :=
  ⟨(innerSL ℝ v.val).smulRight x.val, fun z ↦ by
    rw [ContinuousLinearMap.smulRight_apply, norm_smul, ClosedHemisphere.unit_norm, mul_one]
    exact norm_scalar v z⟩

theorem frame_apply (x : UnitSphere (Vector n)) (z : Vector 1) :
    (frame v x).val z = inner ℝ v.val z • x.val := rfl

theorem column_frame (x : UnitSphere (Vector n)) : column v (frame v x) = x := by
  apply Subtype.ext
  change inner ℝ v.val v.val • x.val = x.val
  rw [real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm, one_pow, one_smul]

theorem frame_column (a : Space n 1) : frame v (column v a) = a := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro z
  rw [frame_apply, column_apply, ← map_smul, scalar_decomposition]

theorem continuous_frame : Continuous (frame (n := n) v) := by
  have h : Continuous (fun x : UnitSphere (Vector n) ↦ (innerSL ℝ v.val).smulRight x.val) := by
    apply continuous_clm_apply.mpr
    intro z
    exact continuous_const.smul continuous_subtype_val
  exact h.subtype_mk _

def homeomorph : Space n 1 ≃ₜ UnitSphere (Vector n) where
  toFun := column v
  invFun := frame v
  left_inv := frame_column v
  right_inv := column_frame v
  continuous_toFun := (column v).continuous
  continuous_invFun := continuous_frame v

end NoExoticSixSphere.Stiefel.OneColumn

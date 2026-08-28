import Wikipedia.NoExoticSixSphere.QuaternionSphere
import Wikipedia.NoExoticSixSphere.SphereCylinderVector
import Wikipedia.NoExoticSixSphere.PartialFrames

/-!
# A smooth actual tangent frame on the original three-sphere

Left multiplication of the imaginary quaternion axes by the unit quaternion
corresponding to the sphere point gives three orthonormal tangent vectors.
The operator extends linearly in the ambient sphere coordinate, so its
smoothness is not obtained by choosing pointwise tangent bases.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Quaternion RealInnerProductSpace

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization

def imaginary : Vector 3 →L[ℝ] ℍ :=
  Quaternion.linearIsometryEquivTuple.symm.toContinuousLinearMap.comp
    ((SphereCylinder.join 2).toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ (Vector 3)))

theorem imaginary_re (v : Vector 3) : (imaginary v).re = 0 := rfl

theorem norm_imaginary (v : Vector 3) : ‖imaginary v‖ = ‖v‖ := by
  change ‖Quaternion.linearIsometryEquivTuple.symm (SphereCylinder.join 2 (0, v))‖ = ‖v‖
  rw [Quaternion.linearIsometryEquivTuple.symm.norm_map]
  have h := SphereCylinder.norm_join_sq 2 0 v
  nlinarith [norm_nonneg (SphereCylinder.join 2 (0, v)), norm_nonneg v]

def operator (x : Vector 4) : Vector 3 →L[ℝ] Vector 4 :=
  Quaternion.linearIsometryEquivTuple.toContinuousLinearMap.comp
    ((ContinuousLinearMap.mul ℝ ℍ (Quaternion.linearIsometryEquivTuple.symm x)).comp imaginary)

theorem operator_apply (x : Vector 4) (v : Vector 3) :
    operator x v = Quaternion.linearIsometryEquivTuple
      (Quaternion.linearIsometryEquivTuple.symm x * imaginary v) := rfl

theorem contDiff_operator : ContDiff ℝ ∞ operator :=
  contDiff_const.clm_comp
    (((ContinuousLinearMap.mul ℝ ℍ).contDiff.comp
      Quaternion.linearIsometryEquivTuple.symm.contDiff).clm_comp contDiff_const)

def quaternionLeftIsometry (s : Sphere 3) : ℍ →ₗᵢ[ℝ] ℍ where
  toLinearMap :=
    (ContinuousLinearMap.mul ℝ ℍ (Quaternion.linearIsometryEquivTuple.symm s.val)).toLinearMap
  norm_map' v := by
    change ‖Quaternion.linearIsometryEquivTuple.symm s.val * v‖ = ‖v‖
    rw [norm_mul, Quaternion.linearIsometryEquivTuple.symm.norm_map,
      ClosedHemisphere.unit_norm, one_mul]

theorem operator_norm (s : Sphere 3) (v : Vector 3) : ‖operator s.val v‖ = ‖v‖ := by
  rw [operator_apply, Quaternion.linearIsometryEquivTuple.norm_map]
  change ‖quaternionLeftIsometry s (imaginary v)‖ = ‖v‖
  rw [(quaternionLeftIsometry s).norm_map, norm_imaginary]

theorem inner_operator (s : Sphere 3) (v : Vector 3) : inner ℝ s.val (operator s.val v) = 0 := by
  have hs : s.val = Quaternion.linearIsometryEquivTuple (quaternionLeftIsometry s 1) := by
    change s.val = Quaternion.linearIsometryEquivTuple
      (Quaternion.linearIsometryEquivTuple.symm s.val * 1)
    rw [mul_one, LinearIsometryEquiv.apply_symm_apply]
  rw [operator_apply]
  change inner ℝ s.val (Quaternion.linearIsometryEquivTuple
    (quaternionLeftIsometry s (imaginary v))) = 0
  rw [hs, Quaternion.linearIsometryEquivTuple.inner_map_map,
    (quaternionLeftIsometry s).inner_map_map]
  simp only [Quaternion.inner_def, one_mul, Quaternion.re_star, imaginary_re]

def frame (s : Sphere 3) : Stiefel.Space 4 3 := ⟨operator s.val, operator_norm s⟩

theorem contMDiff_frame :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector 4) ∞ (fun s : Sphere 3 ↦ (frame s).val) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact contDiff_operator.contMDiff.comp contMDiff_coe_sphere

theorem continuous_frame : Continuous frame := contMDiff_frame.continuous.subtype_mk _

theorem range_operator (s : Sphere 3) : (operator s.val).range = (ℝ ∙ s.val)ᗮ := by
  have hle : (operator s.val).range ≤ (ℝ ∙ s.val)ᗮ := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_operator s v)
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hinj : Injective (operator s.val) := Stiefel.injective (frame s)
  rw [LinearMap.finrank_range_of_inj hinj,
    finrank_euclideanSpace_fin]
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere s)).symm

end NoExoticSixSphere.SphereThreeTangentFrame

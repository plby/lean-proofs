import Wikipedia.NoExoticSixSphere.OrthogonalRotations
import Wikipedia.NoExoticSixSphere.EquatorDimension

/-!
# The actual reflection family on a unit sphere

For a fixed unit vector `w`, reflect it in the hyperplane perpendicular to
the variable unit vector and negate. This is a continuous sphere map, with
the explicit quadratic formula and naturality under actual linear isometries.
-/

noncomputable section

namespace NoExoticSixSphere.SphereReflection

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def negative (w : UnitSphere E) : C(UnitSphere E, UnitSphere E) where
  toFun x := ⟨-hyperplaneReflectionOperator x.val w.val, by
    rw [Metric.mem_sphere, dist_zero_right, norm_neg]
    exact ((ℝ ∙ x.val)ᗮ.reflection.norm_map w.val).trans (ClosedHemisphere.unit_norm w)⟩
  continuous_toFun := by
    have h := continuous_hyperplaneReflectionOperator (fun x : UnitSphere E ↦ x.val)
      continuous_subtype_val ne_zero_of_mem_unit_sphere
    exact (h.clm_apply continuous_const).neg.subtype_mk (fun x ↦ by
      rw [Metric.mem_sphere, dist_zero_right]
      change ‖-hyperplaneReflectionOperator x.val w.val‖ = 1
      rw [norm_neg]
      exact ((ℝ ∙ x.val)ᗮ.reflection.norm_map w.val).trans (ClosedHemisphere.unit_norm w))

theorem negative_apply (w x : UnitSphere E) :
    (negative w x).val = (2 * inner ℝ x.val w.val) • x.val - w.val := by
  change -hyperplaneReflectionOperator x.val w.val = _
  rw [hyperplaneReflectionOperator_apply]
  simp only [ClosedHemisphere.unit_norm, one_pow, inv_one, mul_one, neg_sub]

theorem negative_natural (L : E ≃ₗᵢ[ℝ] F) (w x : UnitSphere E) :
    negative (unitSphereCongr L w) (unitSphereCongr L x) =
      unitSphereCongr L (negative w x) := by
  apply Subtype.ext
  rw [negative_apply]
  change (2 * inner ℝ (L x.val) (L w.val)) • L x.val - L w.val = L (negative w x).val
  rw [L.inner_map_map, negative_apply, map_sub, map_smul]

theorem negative_conjugacy (L : E ≃ₗᵢ[ℝ] F) (w : UnitSphere E) :
    negative w = ((unitSphereCongr L).symm : C(UnitSphere F, UnitSphere E)).comp
      ((negative (unitSphereCongr L w)).comp
        (unitSphereCongr L : C(UnitSphere E, UnitSphere F))) := by
  apply ContinuousMap.ext
  intro x
  apply (unitSphereCongr L).injective
  change unitSphereCongr L (negative w x) =
    unitSphereCongr L ((unitSphereCongr L).symm
      (negative (unitSphereCongr L w) (unitSphereCongr L x)))
  rw [Homeomorph.apply_symm_apply, negative_natural]

end NoExoticSixSphere.SphereReflection

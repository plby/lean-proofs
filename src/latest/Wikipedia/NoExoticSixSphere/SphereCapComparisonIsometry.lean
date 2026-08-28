import Wikipedia.NoExoticSixSphere.SphereCapComparisonLinearFormula

/-!
# The cap comparison at scale two is a native linear-isometry diffeomorphism

This identifies the entire map, including the collapsed pole, with the
restriction of an actual norm-preserving linear equivalence. Its determinant
and its effect on the source-twisted frame parity are not assumed.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization Wikipedia.SmoothSixDPoincare.SphereCoordinates

theorem capTailIsometry_orthogonal (v : Vector 3) :
    inner ℝ capReferencePole.val (capTailIsometry v).val = 0 := by
  have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (capTailIsometry v).property
  simpa only [inner_neg_left, neg_eq_zero] using h

theorem capComparisonLinear_norm (x : Vector 4) : ‖capComparisonLinear x‖ = ‖x‖ := by
  have ho : inner ℝ ((-x 0) • capReferencePole.val)
      (capTailIsometry (SphereCylinder.tail 2 x)).val = 0 := by
    rw [real_inner_smul_left, capTailIsometry_orthogonal, mul_zero]
  have hu : ‖(capTailIsometry (SphereCylinder.tail 2 x)).val‖ =
      ‖SphereCylinder.tail 2 x‖ := capTailIsometry.norm_map _
  have hp : ‖(-x 0) • capReferencePole.val +
      (capTailIsometry (SphereCylinder.tail 2 x)).val‖ ^ 2 =
      ‖(-x 0) • capReferencePole.val‖ ^ 2 +
      ‖(capTailIsometry (SphereCylinder.tail 2 x)).val‖ ^ 2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho
  have hs : ‖capComparisonLinear x‖ ^ 2 = (x 0) ^ 2 + ‖SphereCylinder.tail 2 x‖ ^ 2 := by
    rw [capComparisonLinear_apply, hp,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ClosedHemisphere.unit_norm, one_pow,
      mul_one, neg_sq, hu]
  have he := SphereCylinder.norm_join_sq 2 (x 0) (SphereCylinder.tail 2 x)
  rw [join_head_tail] at he
  nlinarith [norm_nonneg (capComparisonLinear x), norm_nonneg x]

def capComparisonIsometry : Vector 4 →ₗᵢ[ℝ] Vector 4 where
  toLinearMap := capComparisonLinear
  norm_map' := capComparisonLinear_norm

def capComparisonLinearEquiv : Vector 4 ≃ₗᵢ[ℝ] Vector 4 :=
  LinearIsometryEquiv.ofSurjective capComparisonIsometry
    (LinearMap.surjective_of_injective capComparisonIsometry.injective)

theorem capComparisonLinear_base :
    capComparisonLinear (antipode pinchPole).val = capReferencePole.val := by
  have hh : (antipode pinchPole).val 0 = -1 := by simp [antipode, pinchPole, spherePole]
  have ht : SphereCylinder.tail 2 (antipode pinchPole).val = 0 := by
    ext i
    simp [SphereCylinder.tail_apply, antipode, pinchPole, spherePole]
  rw [capComparisonLinear_apply, hh, ht, map_zero, Submodule.coe_zero, add_zero]
  norm_num

theorem capPinchComparison_two_val (x : Sphere 3) :
    (capPinchComparison 2 (by norm_num) x).val = capComparisonLinear x.val := by
  by_cases hx : x = antipode pinchPole
  · subst x
    rw [capPinchComparison_base, capComparisonLinear_base, referenceChart_zero]
  · have ht : x ∈ (pinchScaledChart 2 (by norm_num)).target := by
      rw [pinchScaledChart_target]
      exact hx
    obtain ⟨v, rfl⟩ : ∃ v, pinchScaledChart 2 (by norm_num) v = x :=
      ⟨(pinchScaledChart 2 (by norm_num)).symm x,
        (pinchScaledChart 2 (by norm_num)).right_inv ht⟩
    rw [capPinchComparison_finite, capComparisonLinear_finite]

def capComparisonDiffeomorph : Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact ofLinearIsometry capComparisonLinearEquiv

theorem capComparisonDiffeomorph_apply (x : Sphere 3) :
    capComparisonDiffeomorph x = capPinchComparison 2 (by norm_num) x := by
  apply Subtype.ext
  exact (capPinchComparison_two_val x).symm

theorem contMDiff_capPinchComparison_two :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (capPinchComparison 2 (by norm_num)) := by
  have he : (capPinchComparison 2 (by norm_num) : Sphere 3 → Sphere 3) =
      capComparisonDiffeomorph := funext fun x ↦ (capComparisonDiffeomorph_apply x).symm
  rw [he]
  exact capComparisonDiffeomorph.contMDiff_toFun

end NoExoticSixSphere.SphereSumNeck

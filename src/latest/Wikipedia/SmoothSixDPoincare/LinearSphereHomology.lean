import Wikipedia.SmoothSixDPoincare.LinearSphereHomotopy
import Wikipedia.SmoothSixDPoincare.SphereReflectionHomology
import Mathlib.Data.Sign.Basic

/-!
# Determinant sign computes the actual normalized linear sphere action

Positive determinant joins the identity; negative determinant joins the
literal first-coordinate reflection. The resulting formula concerns the
native integral singular homology map, not an abstract degree assignment.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.LinearSphereAction

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

theorem sphereMap_reflection (n : ℕ) :
    sphereMap (SphereReflection.linearReflection n).toContinuousLinearEquiv.toContinuousLinearMap
      (SphereReflection.linearReflection n).injective = SphereReflection.sphereMap n := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change ‖SphereReflection.linearReflection n x.val‖⁻¹ •
      SphereReflection.linearReflection n x.val = SphereReflection.linearReflection n x.val
  rw [LinearIsometryEquiv.norm_map, unitSphere_norm, inv_one, one_smul]

theorem homology_of_det_pos (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : 0 < A.toLinearEquiv.toLinearMap.det) (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 1)) k) :
    singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective) k a = a := by
  have hh := homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis
    A (ContinuousLinearEquiv.refl ℝ _) (by
      change 0 < A.toLinearEquiv.toLinearMap.det * (LinearMap.id : _ →ₗ[ℝ] _).det
      rwa [LinearMap.det_id, mul_one])
  rw [homotopic_homologyMap hh k]
  change singularHomologyMap (sphereMap (ContinuousLinearMap.id ℝ _) Function.injective_id) k a = a
  rw [sphereMap_id, singularHomologyMap_id]
  rfl

theorem homology_of_det_neg (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (h : A.toLinearEquiv.toLinearMap.det < 0) (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 1)) (k + 1)) :
    singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective) (k + 1) a = -a := by
  have hh := homotopic_of_det_mul_pos (EuclideanSpace.basisFun (Fin (n + 2)) ℝ).toBasis
    A (SphereReflection.linearReflection n).toContinuousLinearEquiv (by
      change 0 < A.toLinearEquiv.toLinearMap.det *
        (SphereReflection.linearReflection n).toLinearMap.det
      rw [SphereReflection.linearReflection_det, mul_neg_one]
      exact neg_pos.mpr h)
  rw [homotopic_homologyMap hh (k + 1), sphereMap_reflection, SphereReflection.sphereMap_homology]

/-- Every invertible linear operator acts by its determinant sign in positive sphere homology. -/
theorem homology_eq_sign_smul (n : ℕ)
    (A : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
    (k : ℕ) (a : SingularHomology (UnitSphere (n + 1)) (k + 1)) :
    singularHomologyMap (sphereMap A.toContinuousLinearMap A.injective) (k + 1) a =
      (SignType.sign A.toLinearEquiv.toLinearMap.det : ℤ) • a := by
  have hd : A.toLinearEquiv.toLinearMap.det ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  obtain hn | hp := lt_or_gt_of_ne hd
  · rw [homology_of_det_neg n A hn, sign_eq_neg_one_iff.mpr hn]
    simp
  · rw [homology_of_det_pos n A hp, sign_eq_one_iff.mpr hp]
    simp

end Wikipedia.SmoothSixDPoincare.LinearSphereAction

import Wikipedia.SmoothSixDPoincare.SphereNormalChartJacobian
import Mathlib.Data.Sign.Basic

/-!
# Positive scaling preserves the actual normal intersection sign

The fixed outward-normal convention uses the inverse normal derivative.
Its Jacobian changes by the reciprocal of the positive scaling determinant.
The resulting sign is therefore unchanged, with the reference frame fixed.
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

variable {V N : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

omit [FiniteDimensional ℝ N] in
theorem normalDerivative_smul_isInvertible
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : c ≠ 0) : (c • A).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := c⁻¹ • A.inverse)
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.self_apply_inverse, hc]
  · ext y
    simp [ContinuousLinearMap.comp_apply, smul_smul, hA.inverse_apply_self, hc]

/-- Exact determinant relation with the original reference frame unchanged. -/
theorem normalJacobian_smul_mul_pow (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : c ≠ 0) :
    normalJacobian j x (c • A) * c ^ Module.finrank ℝ N = normalJacobian j x A := by
  have hB := normalDerivative_smul_isInvertible A hA c hc
  have hcomp : A.comp A.inverse = ContinuousLinearMap.id ℝ N := by
    ext y
    exact hA.self_apply_inverse y
  have hdet : ((c • A).comp A.inverse).det = c ^ Module.finrank ℝ N := by
    rw [ContinuousLinearMap.smul_comp, hcomp]
    change (c • (LinearMap.id : N →ₗ[ℝ] N)).det = _
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hid : (A.comp A.inverse).det = 1 := by
    rw [hcomp]
    exact LinearMap.det_id
  have h := (normalJacobian_mul_chartDet j x (c • A) hB A.inverse).trans
    (normalJacobian_mul_chartDet j x A hA A.inverse).symm
  simpa only [hdet, hid, mul_one] using h

/-- Positive physical-coordinate scaling leaves the signed crossing unchanged. -/
theorem sign_normalJacobian_smul_pos (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (c : ℝ) (hc : 0 < c) :
    SignType.sign (normalJacobian j x (c • A)) = SignType.sign (normalJacobian j x A) := by
  have h := congrArg SignType.sign (normalJacobian_smul_mul_pow j x A hA c hc.ne')
  have hp : SignType.sign (c ^ Module.finrank ℝ N) = 1 := sign_eq_one_iff.mpr (pow_pos hc _)
  simpa only [sign_mul, hp, mul_one] using h

end Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

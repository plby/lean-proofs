import Wikipedia.SmoothSixDPoincare.SphereNormalJacobian

/-!
# Comparison with an actual sphere chart

The radial frame of a sphere parametrization factors as the inverse-normal
frame times its normal derivative. Taking determinants identifies the fixed
normal sign with the ordinary normal Jacobian in any oriented local chart.
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

variable {V N : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

/-- The outward radial vector followed by the actual sphere-parametrization tangent map. -/
def radialFrame (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) : (ℝ × N) →L[ℝ] V :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (x : V)).coprod
    ((inclusionDerivative x).comp C)

theorem normalFrame_comp_normalDerivative (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (normalFrame x A).comp ((ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)) =
      radialFrame x C := by
  apply ContinuousLinearMap.ext
  intro z
  change z.1 • (x : V) + inclusionDerivative x (A.inverse (A (C z.2))) =
    z.1 • (x : V) + inclusionDerivative x (C z.2)
  rw [hA.inverse_apply_self]

/-- A genuine tangent parametrization and the outward vector span the ambient space. -/
theorem bijective_radialFrame (x : Metric.sphere (0 : V) 1)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) (hC : C.IsInvertible) :
    Bijective (radialFrame x C) := by
  have heq : radialFrame x C = normalFrame x C.inverse := by
    apply ContinuousLinearMap.ext
    intro z
    change z.1 • (x : V) + inclusionDerivative x (C z.2) =
      z.1 • (x : V) + inclusionDerivative x (C.inverse.inverse z.2)
    rw [hC.inverse_inverse]
  rw [heq]
  exact bijective_normalFrame x C.inverse hC.inverse

variable [FiniteDimensional ℝ N]

/-- The chart's radial orientation determinant is the fixed normal Jacobian times its
ordinary normal-coordinate determinant. -/
theorem normalJacobian_mul_chartDet (j : (ℝ × N) ≃L[ℝ] V)
    (x : Metric.sphere (0 : V) 1)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] N) (hA : A.IsInvertible)
    (C : N →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    normalJacobian j x A * (A.comp C).det =
      ((radialFrame x C).comp j.symm.toContinuousLinearMap).det := by
  let R : (ℝ × N) →L[ℝ] (ℝ × N) := (ContinuousLinearMap.id ℝ ℝ).prodMap (A.comp C)
  let T : V →L[ℝ] V := j.toContinuousLinearMap.comp (R.comp j.symm.toContinuousLinearMap)
  have hdetT : T.det = (A.comp C).det := by
    have hconj : T.det = R.det := LinearMap.det_conj R.toLinearMap j.toLinearEquiv
    rw [hconj]
    change (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (A.comp C).toLinearMap).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul]
  have hfactor : ((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T =
      (radialFrame x C).comp j.symm.toContinuousLinearMap := by
    have h := normalFrame_comp_normalDerivative x A hA C
    ext v
    change normalFrame x A (j.symm (j (R (j.symm v)))) = radialFrame x C (j.symm v)
    rw [j.symm_apply_apply]
    exact congrArg (fun L : (ℝ × N) →L[ℝ] V => L (j.symm v)) h
  calc
    normalJacobian j x A * (A.comp C).det =
        (((normalFrame x A).comp j.symm.toContinuousLinearMap).comp T).det := by
      rw [← hdetT]
      exact (LinearMap.det_comp _ _).symm
    _ = _ := congrArg ContinuousLinearMap.det hfactor

end Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

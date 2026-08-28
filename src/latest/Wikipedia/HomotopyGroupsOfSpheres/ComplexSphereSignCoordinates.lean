import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductSeedTangent
import Wikipedia.HomotopyGroupsOfSpheres.ComplexSphereScalarCoordinates

/-! # The sign symmetries transport the actual sphere charts and differentials -/

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)

def signComplexEquiv (x y : Bool) : Ambient ≃ₗ[ℂ] Ambient where
  toFun v := WithLp.toLp 2 (signVector x y v)
  invFun v := WithLp.toLp 2 (signVector x y v)
  left_inv v := by
    apply PiLp.ext
    intro r
    change signs x y r * (signs x y r * v r) = v r
    rw [← mul_assoc, ← pow_two, signs_sq, one_mul]
  right_inv v := by
    apply PiLp.ext
    intro r
    change signs x y r * (signs x y r * v r) = v r
    rw [← mul_assoc, ← pow_two, signs_sq, one_mul]
  map_add' v w := by
    apply PiLp.ext
    intro r
    exact mul_add _ _ _
  map_smul' c v := by
    apply PiLp.ext
    intro r
    change signs x y r * (c * v r) = c * (signs x y r * v r)
    ring

def signRealIsometry (x y : Bool) : Ambient ≃ₗᵢ[ℝ] Ambient where
  __ := (signComplexEquiv x y).restrictScalars ℝ
  norm_map' v := by
    change ‖signComplexEquiv x y v‖ = ‖v‖
    have he := normPolynomial_signVector x y v
    change normPolynomial (signComplexEquiv x y v) = normPolynomial v at he
    rw [normPolynomial_eq_norm_sq, normPolynomial_eq_norm_sq] at he
    have hr : ‖signComplexEquiv x y v‖ ^ 2 = ‖v‖ ^ 2 := Complex.ofReal_injective he
    nlinarith [norm_nonneg (signComplexEquiv x y v), norm_nonneg v]

theorem signRealIsometry_apply (x y : Bool) (v : Ambient) (r : Fin 3) :
    signRealIsometry x y v r = signs x y r * v r := rfl

theorem signRealIsometry_det_pos (x y : Bool) :
    0 < (signRealIsometry x y).toLinearEquiv.toLinearMap.det := by
  change 0 < ((signComplexEquiv x y).toLinearMap.restrictScalars ℝ).det
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  exact Complex.normSq_pos.mpr (signComplexEquiv x y).isUnit_det'.ne_zero

theorem sign_sphereIsometry (x y : Bool) (z : UnitSphere) :
    SphereCenteredCoordinates.sphereIsometry (signRealIsometry x y) z = signSphere x y z := by
  apply Subtype.ext
  rfl

def signTangentEquiv (x y : Bool) (z : UnitSphere) :
    SphereCenteredCoordinates.Tangent z ≃ₗᵢ[ℝ]
      SphereCenteredCoordinates.Tangent (signSphere x y z) := by
  have e := SphereCenteredCoordinates.tangentIsometry (signRealIsometry x y) z
  rw [sign_sphereIsometry] at e
  exact e

theorem signTangentEquiv_val (x y : Bool) (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) (r : Fin 3) :
    (signTangentEquiv x y z v).val r = signs x y r * v.val r := by
  unfold signTangentEquiv
  rfl

theorem inverse_signTangentEquiv (x y : Bool) (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) :
    SphereCenteredCoordinates.inverse (signSphere x y z) (signTangentEquiv x y z v) =
      signSphere x y (SphereCenteredCoordinates.inverse z v) := by
  have he := SphereCenteredCoordinates.inverse_tangentIsometry (signRealIsometry x y) z v
  simp only [sign_sphereIsometry] at he
  exact he

theorem sphereSymmetricChart_sign (x y : Bool) (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) :
    sphereSymmetricChart (signSphere x y z) (signTangentEquiv x y z v) =
      signMatrix x y * sphereSymmetricChart z v * signMatrix x y := by
  unfold sphereSymmetricChart
  rw [inverse_signTangentEquiv, symmetricMap_signSphere]

theorem sphereSymmetricDifferential_sign (x y : Bool) (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) :
    sphereSymmetricDifferential (signSphere x y z) (signTangentEquiv x y z v) =
      signMatrix x y * sphereSymmetricDifferential z v * signMatrix x y := by
  apply Matrix.ext
  intro r s
  have hl := sphereSymmetricDifferential_curve_entry (signSphere x y z)
    (signTangentEquiv x y z v) r s
  have hr := hasDerivAt_matrix_congruence_entry
    (fun t : ℝ ↦ sphereSymmetricChart z (t • v))
    (sphereSymmetricDifferential z v) (signMatrix x y) (signMatrix x y) 0
    (sphereSymmetricDifferential_curve_entry z v) r s
  have he : (fun t : ℝ ↦ (signMatrix x y * sphereSymmetricChart z (t • v) * signMatrix x y) r s) =
      fun t : ℝ ↦ (symmetricMap (SphereCenteredCoordinates.inverse (signSphere x y z)
        (t • signTangentEquiv x y z v))).val.val r s := by
    funext t
    rw [← sphereSymmetricChart_sign, map_smul]
    rfl
  rw [he] at hr
  exact hl.unique hr

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

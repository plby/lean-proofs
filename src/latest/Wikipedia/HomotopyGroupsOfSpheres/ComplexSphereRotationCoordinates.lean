import Wikipedia.HomotopyGroupsOfSpheres.ComplexSphereSignCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.SphereOutwardFrames

/-! # The diagonalizing rotation as an orientation-preserving sphere isometry -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)

def rotationComplexEquiv : Ambient ≃ₗ[ℂ] Ambient where
  toFun v := WithLp.toLp 2 (targetRotation *ᵥ v)
  invFun v := WithLp.toLp 2 (targetRotation *ᵥ v)
  left_inv v := by
    apply PiLp.ext
    intro r
    change (targetRotation *ᵥ (targetRotation *ᵥ v)) r = v r
    rw [Matrix.mulVec_mulVec, targetRotation_mul_self, Matrix.one_mulVec]
  right_inv v := by
    apply PiLp.ext
    intro r
    change (targetRotation *ᵥ (targetRotation *ᵥ v)) r = v r
    rw [Matrix.mulVec_mulVec, targetRotation_mul_self, Matrix.one_mulVec]
  map_add' v w := by
    apply PiLp.ext
    intro r
    exact congrFun (Matrix.mulVec_add targetRotation v w) r
  map_smul' c v := by
    apply PiLp.ext
    intro r
    exact congrFun (Matrix.mulVec_smul targetRotation c v) r

def rotationRealIsometry : Ambient ≃ₗᵢ[ℝ] Ambient where
  __ := rotationComplexEquiv.restrictScalars ℝ
  norm_map' v := by
    change ‖rotationComplexEquiv v‖ = ‖v‖
    have he := normPolynomial_targetRotation v
    change normPolynomial (rotationComplexEquiv v) = normPolynomial v at he
    rw [normPolynomial_eq_norm_sq, normPolynomial_eq_norm_sq] at he
    have hr : ‖rotationComplexEquiv v‖ ^ 2 = ‖v‖ ^ 2 := Complex.ofReal_injective he
    nlinarith [norm_nonneg (rotationComplexEquiv v), norm_nonneg v]

theorem rotationRealIsometry_apply (v : Ambient) :
    rotationRealIsometry v = WithLp.toLp 2 (targetRotation *ᵥ v) := rfl

theorem rotationRealIsometry_det_pos :
    0 < rotationRealIsometry.toLinearEquiv.toLinearMap.det := by
  change 0 < (rotationComplexEquiv.toLinearMap.restrictScalars ℝ).det
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  exact Complex.normSq_pos.mpr rotationComplexEquiv.isUnit_det'.ne_zero

theorem rotation_sphereIsometry (z : UnitSphere) :
    SphereCenteredCoordinates.sphereIsometry rotationRealIsometry z = rotationSphere z := by
  apply Subtype.ext
  rfl

def rotationTangentEquiv (z : UnitSphere) :
    SphereCenteredCoordinates.Tangent z ≃ₗᵢ[ℝ]
      SphereCenteredCoordinates.Tangent (rotationSphere z) := by
  have e := SphereCenteredCoordinates.tangentIsometry rotationRealIsometry z
  rw [rotation_sphereIsometry] at e
  exact e

theorem rotationTangentEquiv_val (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) :
    (rotationTangentEquiv z v).val = rotationRealIsometry v.val := by
  unfold rotationTangentEquiv
  rfl

theorem inverse_rotationTangentEquiv (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) :
    SphereCenteredCoordinates.inverse (rotationSphere z) (rotationTangentEquiv z v) =
      rotationSphere (SphereCenteredCoordinates.inverse z v) := by
  have he := SphereCenteredCoordinates.inverse_tangentIsometry rotationRealIsometry z v
  simp only [rotation_sphereIsometry] at he
  exact he

theorem rotation_outwardFrame_orientation (z : UnitSphere)
    (b : Module.Basis (Fin 5) ℝ (SphereCenteredCoordinates.Tangent z)) :
    (SphereCenteredCoordinates.outwardFrame (rotationSphere z)
      (b.map (rotationTangentEquiv z).toLinearEquiv)).orientation =
        (SphereCenteredCoordinates.outwardFrame z b).orientation := by
  have he := SphereCenteredCoordinates.outwardFrame_orientation_map
    rotationRealIsometry rotationRealIsometry_det_pos z b
  exact he

theorem sign_outwardFrame_orientation (x y : Bool) (z : UnitSphere)
    (b : Module.Basis (Fin 5) ℝ (SphereCenteredCoordinates.Tangent z)) :
    (SphereCenteredCoordinates.outwardFrame (signSphere x y z)
      (b.map (signTangentEquiv x y z).toLinearEquiv)).orientation =
        (SphereCenteredCoordinates.outwardFrame z b).orientation := by
  have he := SphereCenteredCoordinates.outwardFrame_orientation_map
    (signRealIsometry x y) (signRealIsometry_det_pos x y) z b
  exact he

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

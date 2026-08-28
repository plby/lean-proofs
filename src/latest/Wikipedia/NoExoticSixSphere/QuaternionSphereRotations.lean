import Wikipedia.NoExoticSixSphere.QuaternionSphere
import Wikipedia.NoExoticSixSphere.SphereReflectionMap

/-!
# Moving the fixed vector in the quaternion reflection family

Right multiplication by an actual unit quaternion is a real linear isometry.
It carries the real unit to the chosen unit vector, so naturality conjugates
that reflection family to the already identified squaring map.
-/

noncomputable section

open scoped Quaternion

namespace NoExoticSixSphere.QuaternionSphere

def rightIsometry (w : Space) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toLinearEquiv := (Units.mk0 w.val (ne_zero_of_mem_unit_sphere w)).mulRightLinearEquiv ℝ
  norm_map' x := by
    change ‖x * w.val‖ = ‖x‖
    rw [norm_mul, ClosedHemisphere.unit_norm, mul_one]

theorem rightIsometry_apply (w : Space) (x : ℍ) : rightIsometry w x = x * w.val := rfl

theorem rightIsometry_one (w : Space) : unitSphereCongr (rightIsometry w) one = w :=
  Subtype.ext (one_mul _)

theorem negative_one_eq_square : SphereReflection.negative one = square := by
  apply ContinuousMap.ext
  intro x
  exact Subtype.ext (square_reflection x).symm

theorem negative_eq_conjugated_square (w : Space) :
    SphereReflection.negative w = (unitSphereCongr (rightIsometry w) : C(Space, Space)).comp
      (square.comp ((unitSphereCongr (rightIsometry w)).symm : C(Space, Space))) := by
  apply ContinuousMap.ext
  intro x
  have h := SphereReflection.negative_natural (rightIsometry w) one
    ((unitSphereCongr (rightIsometry w)).symm x)
  rw [rightIsometry_one, Homeomorph.apply_symm_apply, negative_one_eq_square] at h
  exact h

end NoExoticSixSphere.QuaternionSphere

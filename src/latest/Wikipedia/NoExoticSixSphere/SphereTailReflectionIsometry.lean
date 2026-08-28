import Wikipedia.NoExoticSixSphere.SpherePinchTailReflection
import Wikipedia.NoExoticSixSphere.SphereLinearDiskExtension

/-! # The actual southern reflection is induced by a linear isometry -/

noncomputable section

open Function

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

def tailReflectionLinearMap : Vector 4 →ₗ[ℝ] Vector 4 where
  toFun x := -reflectHeadVector x
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change - -(x 0 + y 0) = - -x 0 + - -y 0
      ring
    · change -(x j.succ + y j.succ) = -x j.succ + -y j.succ
      ring
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change - -(c * x 0) = c * - -x 0
      ring
    · change -(c * x j.succ) = c * -x j.succ
      ring

def tailReflectionLinearIsometry : Vector 4 →ₗᵢ[ℝ] Vector 4 where
  toLinearMap := tailReflectionLinearMap
  norm_map' x := by
    change ‖-reflectHeadVector x‖ = ‖x‖
    rw [norm_neg, norm_reflectHeadVector]

def tailReflectionLinearEquiv : Vector 4 ≃ₗᵢ[ℝ] Vector 4 :=
  LinearIsometryEquiv.ofSurjective tailReflectionLinearIsometry
    (LinearMap.surjective_of_injective tailReflectionLinearIsometry.injective)

theorem tailReflectionLinearEquiv_sphere (s : Sphere 3) :
    SphereLinearReparametrization.sphereMap tailReflectionLinearEquiv s = tailReflection s := by
  apply Subtype.ext
  rfl

end NoExoticSixSphere.SphereSumNeck

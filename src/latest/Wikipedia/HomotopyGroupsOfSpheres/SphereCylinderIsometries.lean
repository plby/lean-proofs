import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries
import Wikipedia.NoExoticSixSphere.SphereCylinderCoordinates
import Mathlib.LinearAlgebra.Determinant

/-!
# Extending sphere isometries through a cylinder direction

The added real coordinate is fixed. The resulting ambient isometry has
the original determinant and commutes with the actual normalized cylinder
map. Iterating this construction retains the orientation comparison.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude

open NoExoticSixSphere
open SphereCenteredCoordinates

variable {n : ℕ}

def liftIsometry (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) where
  __ := ((SphereCylinder.join n).symm.toLinearEquiv.trans
    ((LinearEquiv.refl ℝ ℝ).prodCongr e.toLinearEquiv)).trans
      (SphereCylinder.join n).toLinearEquiv
  norm_map' w := by
    obtain ⟨⟨s, v⟩, rfl⟩ := (SphereCylinder.join n).surjective w
    change ‖SphereCylinder.join n (s, e v)‖ = ‖SphereCylinder.join n (s, v)‖
    have h₁ := SphereCylinder.norm_join_sq n s (e v)
    have h₂ := SphereCylinder.norm_join_sq n s v
    rw [e.norm_map] at h₁
    nlinarith [norm_nonneg (SphereCylinder.join n (s, e v)),
      norm_nonneg (SphereCylinder.join n (s, v))]

theorem liftIsometry_join (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    liftIsometry e (SphereCylinder.join n (s, v)) = SphereCylinder.join n (s, e v) := rfl

theorem liftIsometry_det (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n + 1))) :
    (liftIsometry e).toLinearEquiv.toLinearMap.det = e.toLinearEquiv.toLinearMap.det := by
  change ((SphereCylinder.join n).toLinearEquiv.toLinearMap.comp
    ((LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) e.toLinearEquiv.toLinearMap).comp
      (SphereCylinder.join n).symm.toLinearEquiv.toLinearMap)).det = _
  have h := LinearMap.det_conj
    (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) e.toLinearEquiv.toLinearMap)
    (SphereCylinder.join n).toLinearEquiv
  exact h.trans (by rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul])

theorem liftIsometry_vector (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) (x : Sphere n) :
    liftIsometry e (SphereCylinder.vector n (s, x)) =
      SphereCylinder.vector n (s, sphereIsometry e x) := rfl

theorem sphereIsometry_lift_point (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n + 1))) (s : ℝ) (x : Sphere n) :
    sphereIsometry (liftIsometry e) (SphereCylinder.point n (s, x)) =
      SphereCylinder.point n (s, sphereIsometry e x) := by
  apply Subtype.ext
  change liftIsometry e (‖SphereCylinder.vector n (s, x)‖⁻¹ •
    SphereCylinder.vector n (s, x)) =
      ‖SphereCylinder.vector n (s, sphereIsometry e x)‖⁻¹ •
        SphereCylinder.vector n (s, sphereIsometry e x)
  rw [map_smul, liftIsometry_vector]
  rw [← liftIsometry_vector, (liftIsometry e).norm_map]

end Wikipedia.HomotopyGroupsOfSpheres.CylinderLatitude

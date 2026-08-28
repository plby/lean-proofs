import Wikipedia.NoExoticSixSphere.CircleCylinderAmbientTime

/-!
# The actual spatial isometry, radial axes, and endpoint translations

The original endpoint ambient space is included as the spatial block.
Its two orthogonal extra directions are the signed radial circle axis and
the time axis. The endpoint point maps retain their nonzero translations.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization

def spatialIsometry (m : ℕ) : Vector (m + 1) →ₗᵢ[ℝ] Vector (2 + (m + 1)) where
  toLinearMap := ((ambientCoordinates m).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ V (Vector (m + 1))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ V (Vector (m + 1))))).toLinearMap
  norm_map' v := by
    change ‖ambientCoordinates m (WithLp.toLp 2 ((0 : V), v))‖ = ‖v‖
    rw [(ambientCoordinates m).norm_map]
    simp

theorem spatialIsometry_apply (m : ℕ) (v : Vector (m + 1)) :
    spatialIsometry m v = ambientCoordinates m (WithLp.toLp 2 ((0 : V), v)) := rfl

def radialUnit (m : ℕ) (left : Bool) : Vector (2 + (m + 1)) :=
  ambientCoordinates m (WithLp.toLp 2
    ((SphereCylinder.endPole 0 left).val, (0 : Vector (m + 1))))

theorem radialUnit_norm (m : ℕ) (left : Bool) : ‖radialUnit m left‖ = 1 := by
  rw [radialUnit, (ambientCoordinates m).norm_map]
  simp

theorem inner_radialUnit_spatialIsometry (m : ℕ) (left : Bool) (v : Vector (m + 1)) :
    inner ℝ (radialUnit m left) (spatialIsometry m v) = 0 := by
  rw [radialUnit, spatialIsometry_apply, (ambientCoordinates m).inner_map_map]
  simp [WithLp.prod_inner_apply]

theorem inner_radialUnit_timeUnit (m : ℕ) (left : Bool) :
    inner ℝ (radialUnit m left) (timeUnit m) = 0 := by
  rw [real_inner_comm, inner_timeUnit, radialUnit, timeCoordinate_ambientCoordinates]
  rfl

theorem inner_timeUnit_spatialIsometry (m : ℕ) (v : Vector (m + 1)) :
    inner ℝ (timeUnit m) (spatialIsometry m v) = 0 := by
  rw [inner_timeUnit, spatialIsometry_apply, timeCoordinate_ambientCoordinates]
  exact map_zero seamLinear

theorem ambientCoordinates_endpoint (m : ℕ) (left : Bool) (v : Vector (m + 1)) :
    ambientCoordinates m (WithLp.toLp 2 ((SphereCylinder.endPole 0 left).val, v)) =
      radialUnit m left + spatialIsometry m v := by
  rw [radialUnit, spatialIsometry_apply, ← map_add]
  congr 1
  apply WithLp.ofLp_injective
  change ((SphereCylinder.endPole 0 left).val, v) =
    ((SphereCylinder.endPole 0 left).val, (0 : Vector (m + 1))) + (0, v)
  simp

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem euclideanInclusion_left (x : {x : Sphere m // d.leftMap x = b}) :
    euclideanInclusion d (leftInclusion d x) = radialUnit m true + spatialIsometry m x.val.val :=
  ambientCoordinates_endpoint m true x.val.val

theorem euclideanInclusion_right (x : {x : Sphere m // d.rightMap x = b}) :
    euclideanInclusion d (rightInclusion d x) = radialUnit m false + spatialIsometry m x.val.val :=
  ambientCoordinates_endpoint m false x.val.val

end NoExoticSixSphere.CircleCylinder

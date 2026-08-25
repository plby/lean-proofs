import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import StackExchange.Puzzling139335.Basic

/-!
# Actual affine isometries for the singleton coordinate maps
-/

open Set

namespace Puzzling139335.N4TwoOneOne

noncomputable section

def rightIsometry (θ u v : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (ThreeCorners.rayBasis θ).repr.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ !₂[1 - u, 1 - v])

theorem rightIsometry_apply (θ u v : ℝ) (p : Plane) :
    rightIsometry θ u v p = rightMap θ u v p := by
  ext i
  fin_cases i <;>
    simp [rightIsometry, rightMap, eCoord, fCoord,
      OrthonormalBasis.repr_apply_apply, ThreeCorners.rayBasis_zero,
      ThreeCorners.rayBasis_one, ThreeCorners.ray, ThreeCorners.perpRay,
      Schoenflies.Plane.inner_eq] <;> ring

def leftIsometry (θ u v : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (rightIsometry θ u v).trans ReflectionSeparation.vertical

theorem leftIsometry_apply (θ u v : ℝ) (p : Plane) :
    leftIsometry θ u v p = leftMap θ u v p := by
  change ReflectionSeparation.vertical (rightIsometry θ u v p) = _
  rw [rightIsometry_apply]
  ext i
  fin_cases i <;> simp [rightMap, leftMap] <;> ring

theorem rightMap_injective (θ u v : ℝ) : Function.Injective (rightMap θ u v) := by
  intro p q hpq
  apply (rightIsometry θ u v).injective
  rw [rightIsometry_apply, rightIsometry_apply]
  exact hpq

theorem leftMap_injective (θ u v : ℝ) : Function.Injective (leftMap θ u v) := by
  intro p q hpq
  apply (leftIsometry θ u v).injective
  rw [leftIsometry_apply, leftIsometry_apply]
  exact hpq

theorem rightMap_sourceCorner (θ u v : ℝ) :
    rightMap θ u v (sourceCorner θ u v) = corner 2 := by
  have hsq := Real.sin_sq_add_cos_sq θ
  ext i
  fin_cases i <;> simp [rightMap, sourceCorner, eCoord, fCoord, corner]
  · nlinarith only [congrArg (fun x : ℝ => u * x) hsq]
  · nlinarith only [congrArg (fun x : ℝ => v * x) hsq]

theorem leftMap_sourceCorner (θ u v : ℝ) :
    leftMap θ u v (sourceCorner θ u v) = corner 3 := by
  have hsq := Real.sin_sq_add_cos_sq θ
  ext i
  fin_cases i <;> simp [leftMap, sourceCorner, eCoord, fCoord, corner]
  · nlinarith only [congrArg (fun x : ℝ => u * x) hsq]
  · nlinarith only [congrArg (fun x : ℝ => v * x) hsq]

end

end Puzzling139335.N4TwoOneOne

import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.SquareGeometry

/-!
# Elementary symmetries of the square

Coordinate reflections put an arbitrary square corner at the origin.
They are constructed as actual Euclidean affine isometries.
-/

open Set

namespace Puzzling139335.SquareSymmetry

noncomputable section

/-- Reflect each coordinate whose chosen corner coordinate is one. -/
def cornerFlipPoint (a : Fin 4) (p : Plane) : Plane :=
  !₂[if corner a 0 = 0 then p 0 else 1 - p 0,
    if corner a 1 = 0 then p 1 else 1 - p 1]

theorem cornerFlipPoint_involutive (a : Fin 4) :
    Function.Involutive (cornerFlipPoint a) := by
  intro p
  ext i
  fin_cases i <;>
    simp only [cornerFlipPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  · split <;> simp_all
  · split <;> simp_all

theorem cornerFlipPoint_isometry (a : Fin 4) : Isometry (cornerFlipPoint a) := by
  apply isometry_iff_dist_eq.mpr
  intro p q
  apply (sq_eq_sq₀ (dist_nonneg) (dist_nonneg)).mp
  simp only [plane_dist_sq, cornerFlipPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  split <;> split <;> ring

/-- The coordinate reflection sending `corner a` to the origin. -/
def cornerFlip (a : Fin 4) : Plane ≃ᵃⁱ[ℝ] Plane :=
  ({ toFun := cornerFlipPoint a
     invFun := cornerFlipPoint a
     left_inv := cornerFlipPoint_involutive a
     right_inv := cornerFlipPoint_involutive a
     isometry_toFun := cornerFlipPoint_isometry a } : Plane ≃ᵢ Plane).toRealAffineIsometryEquiv

@[simp] theorem cornerFlip_apply (a : Fin 4) (p : Plane) :
    cornerFlip a p = cornerFlipPoint a p := rfl

@[simp] theorem cornerFlip_corner (a : Fin 4) : cornerFlip a (corner a) = 0 := by
  fin_cases a <;> ext i <;> fin_cases i <;>
    norm_num [cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem cornerFlip_zero (a : Fin 4) : cornerFlip a 0 = corner a := by
  fin_cases a <;> ext i <;> fin_cases i <;>
    norm_num [cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem cornerFlip_center (a : Fin 4) :
    cornerFlip a squareCenter = squareCenter := by
  ext i
  fin_cases i <;> norm_num [cornerFlipPoint, squareCenter]

@[simp] theorem cornerFlip_involutive (a : Fin 4) (p : Plane) :
    cornerFlip a (cornerFlip a p) = p := cornerFlipPoint_involutive a p

theorem cornerFlip_mem_unitSquare (a : Fin 4) {p : Plane} :
    cornerFlip a p ∈ unitSquare ↔ p ∈ unitSquare := by
  have hcoord (x : ℝ) : 1 - x ∈ Icc (0 : ℝ) 1 ↔ x ∈ Icc (0 : ℝ) 1 := by
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  simp only [unitSquare, mem_setOf_eq, cornerFlip_apply, cornerFlipPoint,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  split <;> split <;> simp only [hcoord]

theorem cornerFlip_image_unitSquare (a : Fin 4) :
    cornerFlip a '' unitSquare = unitSquare := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (cornerFlip_mem_unitSquare a).mpr hq
  · intro hp
    exact ⟨cornerFlip a p, (cornerFlip_mem_unitSquare a).mpr hp,
      cornerFlip_involutive a p⟩

/-- Even inclusion of an isometric image of the whole square forces its
center to be fixed, by preservation of a diameter pair. -/
theorem center_fixed_of_maps_square_into_square (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare ⊆ unitSquare) : e squareCenter = squareCenter := by
  apply affineIsometry_map_squareCenter_of_diameter_pair e
    (corner_mem_unitSquare 0) (corner_mem_unitSquare (0 + 2))
  · exact he (mem_image_of_mem e (corner_mem_unitSquare 0))
  · exact he (mem_image_of_mem e (corner_mem_unitSquare (0 + 2)))
  · exact corner_opposite_dist_sq 0

theorem center_fixed_of_preserves_square (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' unitSquare = unitSquare) : e squareCenter = squareCenter :=
  center_fixed_of_maps_square_into_square e he.subset

end

end Puzzling139335.SquareSymmetry

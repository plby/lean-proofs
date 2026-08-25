import StackExchange.Puzzling139335.Definitions

/-! # Function iterates and powers of actual plane isometries -/

open Set

namespace Puzzling139335.QuarterTurnTopology

/-- Group powers of affine isometries act by the corresponding function iterates. -/
theorem affineIsometry_coe_pow (e : Plane ≃ᵃⁱ[ℝ] Plane) (n : ℕ) :
    ((e ^ n : Plane ≃ᵃⁱ[ℝ] Plane) : Plane → Plane) = (e : Plane → Plane)^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) e n

/-- A function-iterate image is an image by a genuine affine isometry. -/
theorem affineIsometry_pow_image (e : Plane ≃ᵃⁱ[ℝ] Plane) (n : ℕ) (T : Set Plane) :
    (e ^ n) '' T = ((e : Plane → Plane)^[n]) '' T := by
  rw [affineIsometry_coe_pow]

/-- The same bridge for powers in the homeomorphism group. -/
theorem homeomorph_coe_pow (e : Plane ≃ₜ Plane) (n : ℕ) :
    ((e ^ n : Plane ≃ₜ Plane) : Plane → Plane) = (e : Plane → Plane)^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) e n

/-- Interiors commute with the actual iterated images used by the quarter-turn theorem. -/
theorem interior_iterate_image (e : Plane ≃ᵃⁱ[ℝ] Plane) (n : ℕ) (T : Set Plane) :
    interior (((e : Plane → Plane)^[n]) '' T) =
      ((e : Plane → Plane)^[n]) '' interior T := by
  rw [← affineIsometry_pow_image, ← affineIsometry_pow_image]
  exact ((e ^ n).toHomeomorph.image_interior T).symm

end Puzzling139335.QuarterTurnTopology

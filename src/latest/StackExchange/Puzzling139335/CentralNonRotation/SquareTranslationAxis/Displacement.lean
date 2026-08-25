import StackExchange.Puzzling139335.Definitions
import Mathlib.Tactic.Abel

/-! # Displacement identities for an isometry whose square is a translation -/

namespace Puzzling139335.CentralNonRotation

open Set

/-- The displacement of a point under an affine isometry. -/
noncomputable def affineDisplacement (g : Plane ≃ᵃⁱ[ℝ] Plane) (x : Plane) : Plane := g x - x

theorem continuous_affineDisplacement (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    Continuous (affineDisplacement g) :=
  g.continuous.sub continuous_id

/-- Applying the isometry reflects its displacement about half the translation
vector of its square. -/
theorem affineDisplacement_apply_of_square_translation
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (v : Plane)
    (hg2 : ∀ x, g (g x) = x + v) (x : Plane) :
    affineDisplacement g (g x) = v - affineDisplacement g x := by
  unfold affineDisplacement
  rw [hg2]
  abel

/-- Point reflection in the domain induces point reflection in displacement
space, centered at the displacement of the original center. -/
theorem affineDisplacement_pointReflection
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (c x : Plane) :
    affineDisplacement g (AffineIsometryEquiv.pointReflection ℝ c x) =
      (affineDisplacement g c + affineDisplacement g c) - affineDisplacement g x := by
  unfold affineDisplacement
  rw [AffineIsometryEquiv.pointReflection_apply, g.map_vadd, g.map_vsub]
  simp only [vsub_eq_sub, vadd_eq_add]
  abel

/-- The center displacement determines the dihedral conjugacy relation. -/
theorem pointReflection_conjugate_eq_symm_of_twice_displacement
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (c v : Plane)
    (hg2 : ∀ x, g (g x) = x + v)
    (hshift : v = (g c - c) + (g c - c)) (x : Plane) :
    AffineIsometryEquiv.pointReflection ℝ c
      (g (AffineIsometryEquiv.pointReflection ℝ c x)) = g.symm x := by
  have hmap (y : Plane) :
      g (AffineIsometryEquiv.pointReflection ℝ c y) =
        AffineIsometryEquiv.pointReflection ℝ (g c) (g y) := by
    rw [AffineIsometryEquiv.pointReflection_apply, g.map_vadd, g.map_vsub,
      AffineIsometryEquiv.pointReflection_apply]
  have hproduct (y : Plane) :
      AffineIsometryEquiv.pointReflection ℝ c
        (g (AffineIsometryEquiv.pointReflection ℝ c (g y))) = y := by
    rw [hmap, hg2, hshift]
    simp only [AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add]
    abel
  simpa only [g.apply_symm_apply] using hproduct (g.symm x)

end Puzzling139335.CentralNonRotation

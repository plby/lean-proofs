import StackExchange.Puzzling139335.N4Axial.Density
import StackExchange.Puzzling139335.TranslationCancellation

/-!
# Dihedral cancellation for the actual middle density sum

This applies directly to the original four-piece dissection. Neither a
Jordan property of the middle union nor a separate finite-contact hypothesis
is needed for its weighted-density symmetry.
-/

open Set MeasureTheory

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

/-- If a middle congruence squares to a nonzero translation and the horizontal
reflection conjugates it to its inverse, the middle pieces are themselves
horizontal reflections. -/
theorem middle_reflected_of_dihedral_translation_square
    (h : Configuration d) (g : Plane ≃ᵃⁱ[ℝ] Plane) (v : Plane) (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v)
    (hconj : ∀ x, ReflectionSeparation.horizontal
      (g (ReflectionSeparation.horizontal x)) = g.symm x)
    (himage : g '' d.piece 2 = d.piece 3) :
    ReflectionSeparation.horizontal '' d.piece 2 = d.piece 3 := by
  have hF : (fun x => weightedDensityReal (d.piece 2)
      (ReflectionSeparation.horizontal x) + weightedDensityReal (g '' d.piece 2)
        (ReflectionSeparation.horizontal x)) =ᵐ[volume]
      (fun x => weightedDensityReal (d.piece 2) x +
        weightedDensityReal (g '' d.piece 2) x) := by
    simpa only [himage] using h.middle_density_sum_reflected_ae
  have heq := (d.jordan 2).image_eq_of_dihedral_density_symmetry g
    ReflectionSeparation.horizontal hv hg2 ReflectionSeparation.horizontal_involutive
    hconj hF
  exact heq.symm.trans himage

/-- The resulting horizontal-reflection pair excludes a protected center. -/
theorem false_of_middle_dihedral_translation_square
    (h : Configuration d) (hc : d.HasProtectedCenter)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (v : Plane) (hv : v ≠ 0)
    (hg2 : ∀ x, g (g x) = x + v)
    (hconj : ∀ x, ReflectionSeparation.horizontal
      (g (ReflectionSeparation.horizontal x)) = g.symm x)
    (himage : g '' d.piece 2 = d.piece 3) : False := by
  have himageH := h.middle_reflected_of_dihedral_translation_square g v hv hg2 hconj himage
  have hnot := d.center_not_mem_fixed_pair (by decide : (2 : Fin 4) ≠ 3)
    ReflectionSeparation.horizontal himageH ReflectionSeparation.horizontal_center
  exact (h.center_in_middle hc).elim hnot.1 hnot.2

end Puzzling139335.N4OuterPair.Configuration

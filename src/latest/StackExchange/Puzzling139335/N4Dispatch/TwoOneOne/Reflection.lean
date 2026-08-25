import StackExchange.Puzzling139335.SquareSymmetry.Eight
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.QuarterTurnPair

/-!
# The reflection forced by an actual top-corner pair

A square symmetry taking the top-right corner to the top-left corner is
either the vertical reflection or a quarter-turn.  An actual quarter-turn
between two dissection pieces excludes a protected center, so the vertical
reflection is the only possibility in a putative counterexample.
-/

open Set

namespace Puzzling139335.N4Dispatch.TwoOneOne

open SquareSymmetry ReflectionSeparation

/-- The two coordinate actions compatible with this ordered corner map. -/
theorem top_corner_map_forms (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hS : e '' unitSquare ⊆ unitSquare)
    (hcorner : e (corner 2) = corner 3) :
    (∀ p, e p = vertical p) ∨ (∀ p, e p = vertical (diagonal p)) := by
  have hx := congrArg (fun p : Plane => p 0) hcorner
  have hy := congrArg (fun p : Plane => p 1) hcorner
  obtain ⟨b, hform | hform⟩ := coordinate_forms_of_maps_square_into_square e hS
  · fin_cases b
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
    · exact Or.inl hform
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
  · fin_cases b
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx
    · exact Or.inr hform
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hy
    · exfalso
      norm_num [hform, cornerFlipPoint, corner, Fin.ext_iff] at hx

/-- The non-reflection alternative has square equal to the central half-turn. -/
theorem quarterTurn_of_top_corner_swap (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hform : ∀ p, e p = vertical (diagonal p)) :
    ∀ p, e (e p) = AffineIsometryEquiv.pointReflection ℝ squareCenter p := by
  intro p
  simp only [hform]
  ext k
  fin_cases k <;>
    simp [AffineIsometryEquiv.pointReflection_apply, squareCenter,
      vsub_eq_sub, vadd_eq_add] <;> ring

/-- An actual congruence taking these top corners to one another must be
the vertical reflection when the dissection has a protected center. -/
theorem vertical_of_top_corner_pair (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece i = d.piece j)
    (hS : e '' unitSquare ⊆ unitSquare)
    (hcorner : e (corner 2) = corner 3) : e = vertical := by
  rcases top_corner_map_forms e hS hcorner with hreflection | hquarter
  · exact AffineIsometryEquiv.ext hreflection
  · exact (d.not_hasProtectedCenter_of_quarterTurn_pair hij e
      (quarterTurn_of_top_corner_swap e hquarter) hS he hc).elim

/-- The image form used by the normalized `2110` corner-incidence case. -/
theorem vertical_image_of_top_corner_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i j : Fin 4} (hij : i ≠ j)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece j)
    (hS : e '' unitSquare ⊆ unitSquare)
    (hcorner : e (corner 2) = corner 3) : vertical '' d.piece i = d.piece j := by
  rwa [vertical_of_top_corner_pair d hc hij e he hS hcorner] at he

end Puzzling139335.N4Dispatch.TwoOneOne

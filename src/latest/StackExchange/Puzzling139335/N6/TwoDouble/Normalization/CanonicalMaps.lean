import StackExchange.Puzzling139335.N6.TwoDouble.SquarePair

/-!
# Canonical maps after placing the full corner pair on the bottom side

The image of the bottom-left corner is known not to belong to the original
piece.  The vertical reflection and the main-diagonal reflection would send
it to an actual bottom corner of that same piece, and are therefore excluded.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

private theorem vertical_corner_zero :
    ReflectionSeparation.vertical (corner 0) = corner 1 := by
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

private theorem diagonal_corner_zero :
    ReflectionSeparation.diagonal (corner 0) = corner 0 := by
  ext k
  fin_cases k <;> norm_num [corner, Fin.ext_iff]

/-- Only the horizontal reflection, anti-diagonal reflection, and central
half-turn remain for this actual, canonically positioned square pair. -/
theorem canonical_square_pair_map_cases (d : SquareDissection)
    (hc : d.HasProtectedCenter) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 1) (hS : e '' unitSquare = unitSquare)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (havoid : e (corner 0) ∉ d.piece 0) :
    e = ReflectionSeparation.horizontal ∨ e = ReflectionSeparation.antiDiagonal ∨
      e = AffineIsometryEquiv.pointReflection ℝ squareCenter := by
  rcases square_pair_map_cases d hc (by decide : (0 : Fin 4) ≠ 1) e he hS with
    hhorizontal | hvertical | hdiagonal | hanti | hhalf
  · exact Or.inl hhorizontal
  · exact False.elim (havoid (by simpa only [hvertical, vertical_corner_zero] using hBR))
  · exact False.elim (havoid (by simpa only [hdiagonal, diagonal_corner_zero] using hBL))
  · exact Or.inr (Or.inl hanti)
  · exact Or.inr (Or.inr hhalf)

/-- The corresponding three possibilities for the actual second piece. -/
theorem canonical_square_pair_image_cases (d : SquareDissection)
    (hc : d.HasProtectedCenter) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 1) (hS : e '' unitSquare = unitSquare)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (havoid : e (corner 0) ∉ d.piece 0) :
    ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1 ∨
      ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 1 ∨
      AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 0 = d.piece 1 := by
  rcases canonical_square_pair_map_cases d hc e he hS hBL hBR havoid with h | h | h
  · exact Or.inl (h ▸ he)
  · exact Or.inr (Or.inl (h ▸ he))
  · exact Or.inr (Or.inr (h ▸ he))

end Puzzling139335.N6.TwoDouble

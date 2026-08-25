import StackExchange.Puzzling139335.N6.TripleEqualParity.SideForcing
import StackExchange.Puzzling139335.N6.TripleEqualParity.Triangle

/-!
# Equal outer parity at a corner split into three equal sectors

These normalized placements cannot occur in a square dissection, even
without the protected-center assumption.  Square containment bounds the
prototype by an explicit quadrilateral.  Coverage forces a right isosceles
triangle's three vertices into the fourth piece.  The triangle cannot fit
the quadrilateral after transporting it back by a congruence.

The hypotheses below describe actual placements, not convex hull chords.
The reduction from the incidence pattern to these placements is separate.
-/

open Set
open Puzzling139335.N6.TripleSectors

namespace Puzzling139335.N6.TripleEqualParity

/-- Exclusion directly from the three exact support bounds. -/
theorem normalized_bounds_impossible (d : SquareDissection)
    (h0 : d.piece 0 ⊆ equalParityBound)
    (h1 : d.piece 1 ⊆ rotateThirty '' equalParityBound)
    (h2 : d.piece 2 ⊆ rotateSixty '' equalParityBound) : False := by
  obtain ⟨ha, hb, hc⟩ := forced_corner_triangle_mem d h0 h1 h2
  exact no_congruent_forced_triangle h0 (d.congruent 0 3) ha hb hc

/-- The equal-outer-parity normalized configuration is impossible, for
either orientation parity of the middle tile. -/
theorem normalized_equal_parity_impossible (d : SquareDissection)
    (houter : d.piece 2 = rotateSixty '' d.piece 0)
    (hmiddle : d.piece 1 = rotateThirty '' d.piece 0 ∨
      d.piece 1 = reflectThirty '' d.piece 0) : False := by
  have h0 : d.piece 0 ⊆ equalParityBound :=
    subset_equalParityBound_of_square_fits (d.piece_subset 0)
      (by rw [← houter]; exact d.piece_subset 2)
  apply normalized_bounds_impossible d h0 (middle_subset_rotated_bound h0 hmiddle)
  rw [houter]
  exact image_mono h0

end Puzzling139335.N6.TripleEqualParity

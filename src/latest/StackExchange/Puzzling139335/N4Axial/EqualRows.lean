import StackExchange.Puzzling139335.N4Axial.EqualRows.Coordinates
import StackExchange.Puzzling139335.N4Axial.VerticalTranslation
import StackExchange.Puzzling139335.N4Axial.HorizontalReflection

/-!
# Equal first rows cannot place both middle tiles against the right side

Right contacts force equal first affine coordinates, not merely equal
linear rows.  The relative congruence then fixes the first coordinate and
is excluded by the vertical-translation and horizontal-reflection results.
-/

open Set

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

/-- The two middle congruences cannot have the same first matrix row when
both middle tiles meet the right side and the center is protected. -/
theorem false_of_middle_right_contact_equal_first_rows
    (h : Configuration d) (hc : d.HasProtectedCenter)
    (e2 e3 : Plane ≃ᵃⁱ[ℝ] Plane)
    (h2 : e2 '' d.piece 0 = d.piece 2)
    (h3 : e3 '' d.piece 0 = d.piece 3)
    (hright2 : (d.piece 2 ∩ {p | p 0 = 1}).Nonempty)
    (hright3 : (d.piece 3 ∩ {p | p 0 = 1}).Nonempty)
    (h00 : PlaneIsometries.linearMatrix e2 0 0 =
      PlaneIsometries.linearMatrix e3 0 0)
    (h01 : PlaneIsometries.linearMatrix e2 0 1 =
      PlaneIsometries.linearMatrix e3 0 1) : False := by
  have hcoord := N4Axial.first_coordinates_eq_of_right_contacts_equal_first_rows
    (d.piece 0) e2 e3
    (by simpa only [h2] using d.piece_subset 2)
    (by simpa only [h3] using d.piece_subset 3)
    (by simpa only [h2] using hright2)
    (by simpa only [h3] using hright3) h00 h01
  let g : Plane ≃ᵃⁱ[ℝ] Plane := e2.symm.trans e3
  have hg0 : ∀ p, (g p) 0 = p 0 := by
    intro p
    simpa [g] using (hcoord (e2.symm p)).symm
  have himage : g '' d.piece 2 = d.piece 3 := by
    rw [← h2, ← h3, image_image]
    congr 1
    funext p
    simp [g]
  obtain ⟨t, hg⟩ | ⟨b, hg⟩ :=
    N4Axial.vertical_translation_or_horizontal_reflection_of_first_coordinate g hg0
  · exact h.false_of_middle_vertical_translation hc g t hg himage
  · exact h.false_of_middle_horizontal_reflection hc g b hg himage

/-- The same obstruction expressed with right-supporting contacts in the
source piece, before applying the two congruences. -/
theorem false_of_middle_equal_first_rows_of_source_right_contacts
    (h : Configuration d) (hc : d.HasProtectedCenter)
    (e2 e3 : Plane ≃ᵃⁱ[ℝ] Plane)
    (h2 : e2 '' d.piece 0 = d.piece 2)
    (h3 : e3 '' d.piece 0 = d.piece 3)
    (hright2 : (d.piece 0 ∩ {p | (e2 p) 0 = 1}).Nonempty)
    (hright3 : (d.piece 0 ∩ {p | (e3 p) 0 = 1}).Nonempty)
    (h00 : PlaneIsometries.linearMatrix e2 0 0 =
      PlaneIsometries.linearMatrix e3 0 0)
    (h01 : PlaneIsometries.linearMatrix e2 0 1 =
      PlaneIsometries.linearMatrix e3 0 1) : False := by
  apply h.false_of_middle_right_contact_equal_first_rows hc e2 e3 h2 h3
    ?_ ?_ h00 h01
  · obtain ⟨p, hp, hpright⟩ := hright2
    exact ⟨e2 p, h2 ▸ mem_image_of_mem e2 hp, hpright⟩
  · obtain ⟨p, hp, hpright⟩ := hright3
    exact ⟨e3 p, h3 ▸ mem_image_of_mem e3 hp, hpright⟩

end Puzzling139335.N4OuterPair.Configuration

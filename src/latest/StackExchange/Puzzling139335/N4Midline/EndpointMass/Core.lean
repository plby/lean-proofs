import StackExchange.Puzzling139335.N4Midline.HalfContainment
import StackExchange.Puzzling139335.BandMass.HalfBands
import StackExchange.Puzzling139335.QuadrantMass
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.Transform

/-!
# The mass obstruction for the two endpoint coordinate forms

The half-turn form keeps both original pieces in the left half-square.
The other form folds complementary portions into the upper-left quarter.
Both arguments use the actual pieces of the given dissection.
-/

open Set

namespace Puzzling139335.SquareDissection

noncomputable section

open N4Midline ReflectionSeparation

/-- The lower-half mass obstruction transported by the diagonal
reflection is the corresponding left-half obstruction. -/
theorem false_of_two_pieces_in_left_half (d : SquareDissection)
    {c i j : Fin 4} (hc : squareCenter ∈ interior (d.piece c))
    (hci : c ≠ i) (hcj : c ≠ j) (hij : i ≠ j)
    (hi : d.piece i ⊆ leftHalfSquare) (hj : d.piece j ⊆ leftHalfSquare) : False := by
  let d' := d.map diagonal diagonal_image_unitSquare
  have hc' : squareCenter ∈ interior (d'.piece c) := by
    change squareCenter ∈ interior (diagonal '' d.piece c)
    have hmem := (mem_interior_image_affineIsometry diagonal).mpr hc
    simpa only [diagonal_center] using hmem
  have hi' : d'.piece i ⊆ horizontalBand 0 (1 / 2) := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hi hp).2, (hi hp).1⟩
  have hj' : d'.piece j ⊆ horizontalBand 0 (1 / 2) := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hj hp).2, (hj hp).1⟩
  exact d'.false_of_two_pieces_in_lower_half hc' hci hcj hij hi' hj'

/-- Either exact upper-left endpoint placement excludes a third piece
containing the center in its interior. -/
theorem false_of_upperLeft_endpoint_coordinates (d : SquareDissection)
    {i j c : Fin 4} (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j)
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : (∀ p, (e p) 0 = (1 / 2 : ℝ) - p 0 ∧ (e p) 1 = 1 - p 1) ∨
      (∀ p, (e p) 0 = p 1 ∧ (e p) 1 = p 0 + 1 / 2))
    (himage : e '' d.piece i = d.piece j)
    (hleft : d.piece i ⊆ leftHalfSquare)
    (hc : squareCenter ∈ interior (d.piece c)) : False := by
  rcases he with hhalf | hrotated
  · have hjleft : d.piece j ⊆ leftHalfSquare := by
      rw [← himage]
      rintro _ ⟨p, hp, rfl⟩
      have hbounds := hleft hp
      change (e p) 0 ∈ Icc (0 : ℝ) (1 / 2) ∧ (e p) 1 ∈ Icc (0 : ℝ) 1
      rw [(hhalf p).1, (hhalf p).2]
      exact ⟨⟨by linarith [hbounds.1.2], by linarith [hbounds.1.1]⟩,
        ⟨by linarith [hbounds.2.2], by linarith [hbounds.2.1]⟩⟩
    exact d.false_of_two_pieces_in_left_half hc hci hcj hij hleft hjleft
  · exact d.false_of_rotated_quadrant_pair hij hci hcj e hrotated himage
      (fun p hp => (hleft hp).1.2) hc

end

end Puzzling139335.SquareDissection

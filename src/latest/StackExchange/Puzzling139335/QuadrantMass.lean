import StackExchange.Puzzling139335.QuadrantMass.Geometry
import StackExchange.Puzzling139335.QuadrantMass.Folding
import StackExchange.Puzzling139335.Mass

/-!
# Saturation by a rotated pair in the upper-left quarter

Let `P` be an original tile contained in the left half-square, and let another
original tile be its image under `(x,y) ↦ (y,x+1/2)`. The upper portion of `P`
and the moved lower portion have total weighted mass one quarter. They fit in
the upper-left quarter, so the two original closed tiles cover that quarter.
Consequently no third tile contains the square center in its interior.

The cut portions need not be Jordan regions. Their masses are the restrictions
of the original density, with the horizontal cut assigned to exactly one side.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335

/-- The two original tiles in the rotated placement cover the upper-left
quarter as an actual closed set, including the square center. -/
theorem SquareDissection.upperLeftQuarter_subset_pair_of_rotated_copy
    (d : SquareDissection) {i j : Fin 4} (hij : i ≠ j)
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : ∀ p, (e p) 0 = p 1 ∧ (e p) 1 = p 0 + 1 / 2)
    (himage : e '' d.piece i = d.piece j)
    (hleft : ∀ p ∈ d.piece i, p 0 ≤ (1 / 2 : ℝ)) :
    upperLeftQuarter ⊆ d.piece i ∪ d.piece j := by
  apply QuadrantMass.container_subset_union_of_folded_mass
    (d.jordan i) (d.jordan j) e himage (d.disjoint_interiors hij)
    measurableSet_upperHalfPlane isClosed_upperLeftQuarter
    closure_interior_upperLeftQuarter
  · rw [volume_upperLeftQuarter_ofReal]
    exact ENNReal.ofReal_ne_top
  · intro p hp
    have hpS := d.piece_subset i hp.1
    exact ⟨⟨hpS.1.1, hleft p hp.1⟩, hp.2, hpS.2.2⟩
  · rintro x ⟨p, ⟨hpP, hpLow⟩, rfl⟩
    have hpS := d.piece_subset i hpP
    have hpLeft := hleft p hpP
    have hpBelow : p 1 < (1 / 2 : ℝ) := lt_of_not_ge hpLow
    change ((0 : ℝ) ≤ (e p) 0 ∧ (e p) 0 ≤ 1 / 2) ∧
      ((1 / 2 : ℝ) ≤ (e p) 1 ∧ (e p) 1 ≤ 1)
    rw [(he p).1, (he p).2]
    exact ⟨⟨hpS.2.1, hpBelow.le⟩, by linarith [hpS.1.1], by linarith⟩
  · rw [volume_upperLeftQuarter, d.piece_weightedMass_eq_quarter]

/-- A third original tile cannot contain the center in its interior in this
rotated-pair placement. -/
theorem SquareDissection.false_of_rotated_quadrant_pair
    (d : SquareDissection) {i j c : Fin 4} (hij : i ≠ j)
    (hci : c ≠ i) (hcj : c ≠ j)
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : ∀ p, (e p) 0 = p 1 ∧ (e p) 1 = p 0 + 1 / 2)
    (himage : e '' d.piece i = d.piece j)
    (hleft : ∀ p ∈ d.piece i, p 0 ≤ (1 / 2 : ℝ))
    (hc : squareCenter ∈ interior (d.piece c)) : False := by
  have hcenter := d.upperLeftQuarter_subset_pair_of_rotated_copy hij e he himage hleft
    squareCenter_mem_upperLeftQuarter
  rcases hcenter with hi | hj
  · exact d.not_mem_other_piece hci hc hi
  · exact d.not_mem_other_piece hcj hc hj

end Puzzling139335

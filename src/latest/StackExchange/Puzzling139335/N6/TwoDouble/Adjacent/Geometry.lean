import StackExchange.Puzzling139335.DoubleCorner
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# The actual acute germ of the adjacent reflected pair

The anti-diagonal reflection fixes the shared bottom-right corner.  The
bottom-left corner selects the lower of the two normalized half-quadrants.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.Adjacent

open ReflectionSeparation SquareSymmetry AcuteCorner DoubleCorner

theorem antiDiagonal_bottom_right : antiDiagonal (corner 1) = corner 1 := by
  apply antiDiagonal_fixed
  norm_num [corner, Fin.ext_iff]

theorem antiDiagonal_bottom_left : antiDiagonal (corner 0) = corner 2 := by
  ext i
  fin_cases i <;> simp [corner]

/-- The two actual reflected source pieces share their bottom-right
corner and have the indicated second endpoint. -/
theorem reflected_corner_memberships (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : antiDiagonal '' d.piece 0 = d.piece 1) :
    corner 1 ∈ d.piece 1 ∧ corner 2 ∈ d.piece 1 := by
  rw [← hanti]
  exact ⟨⟨corner 1, hBR, antiDiagonal_bottom_right⟩,
    ⟨corner 0, hBL, antiDiagonal_bottom_left⟩⟩

/-- The bottom-left endpoint chooses the exact lower half-quadrant germ
at the source's acute corner. -/
theorem source_halfCone (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : antiDiagonal '' d.piece 0 = d.piece 1)
    (hother : ∀ l, l ≠ (0 : Fin 4) → l ≠ 1 → corner 1 ∉ d.piece l) :
    cornerFlip 1 '' d.piece 0 ⊆ cone45 ∧
      SameBoundaryGerm (cornerFlip 1 '' d.piece 0) cone45 0 := by
  have hBR1 := (reflected_corner_memberships d hBL hBR hanti).1
  rcases d.double_corner_normalized_halfCones (by decide : (0 : Fin 4) ≠ 1)
      hBR hBR1 hother antiDiagonal hanti antiDiagonal_bottom_right with h | h
  · exact ⟨h.1, h.2.2.1⟩
  · have hbad := h.1 (mem_image_of_mem (cornerFlip 1) hBL)
    change 0 ≤ cornerFlip 1 (corner 0) 0 ∧
      cornerFlip 1 (corner 0) 0 ≤ cornerFlip 1 (corner 0) 1 at hbad
    norm_num [cornerFlipPoint, corner, Fin.ext_iff] at hbad

/-- Neither member of the reflected pair can contain the center in its
interior. This uses the actual reflection fixing the center. -/
theorem outer_center_excluded (d : SquareDissection)
    (hanti : antiDiagonal '' d.piece 0 = d.piece 1) :
    squareCenter ∉ interior (d.piece 0) ∧
      squareCenter ∉ interior (d.piece 1) :=
  d.center_not_mem_fixed_pair (by decide) antiDiagonal hanti antiDiagonal_center

end Puzzling139335.N6.TwoDouble.Adjacent

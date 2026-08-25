import StackExchange.Puzzling139335.N5.SideExclusion.Dissection
import StackExchange.Puzzling139335.N5.Normalized

/-!
# The remaining normalized pieces avoid the bottom and left sides

The diagonal pair owns the two full sides.  Supporting-side uniqueness
excludes the other pieces from the open sides, while their actual corner
counts exclude the endpoints.  Every point of either remaining piece
therefore has strictly positive coordinates.
-/

open Set

namespace Puzzling139335.N5

/-- Among the remaining two pieces, only the top-right square corner can
occur: the singleton-corner piece owns it and the other piece has no corners. -/
theorem Normalized.remaining_corner_eq_top_right {d : SquareDissection}
    (h : Normalized d) {i c : Fin 4} (hi : i = 2 ∨ i = 3)
    (hc : corner c ∈ d.piece i) : c = 2 := by
  rcases hi with rfl | rfl
  · obtain ⟨a, _, ha⟩ := unique_corner_of_tile_count_one d 2 h.count_two
    exact (ha c hc).trans (ha 2 h.top_right).symm
  · exact (no_corner_of_count_zero d 3 h.count_three c hc).elim

/-- Neither remaining piece contains any of the other three corners. -/
theorem Normalized.remaining_not_mem_corner {d : SquareDissection}
    (h : Normalized d) {i c : Fin 4} (hi : i = 2 ∨ i = 3) (hc : c ≠ 2) :
    corner c ∉ d.piece i :=
  fun hmem => hc (h.remaining_corner_eq_top_right hi hmem)

/-- Both remaining pieces avoid the entire closed bottom side. -/
theorem Normalized.bottom_side_disjoint_remaining {d : SquareDissection}
    (h : Normalized d) {i : Fin 4} (hi : i = 2 ∨ i = 3) :
    Disjoint (segment ℝ (corner 0) (corner 1)) (d.piece i) := by
  apply Set.disjoint_left.mpr
  intro x hx hxi
  have h0i : (0 : Fin 4) ≠ i := by
    rcases hi with rfl | rfl <;> decide
  have hends : x ∉ ({corner 0, corner 1} : Set Plane) := by
    intro hxends
    rcases mem_insert_iff.mp hxends with rfl | hxone
    · exact h.remaining_not_mem_corner hi (by decide : (0 : Fin 4) ≠ 2) hxi
    · obtain rfl := mem_singleton_iff.mp hxone
      exact h.remaining_not_mem_corner hi (by decide : (1 : Fin 4) ≠ 2) hxi
  exact bottom_open_not_mem_of_bottom_segment d h0i h.bottom_left_sides.1
    ⟨hx, hends⟩ hxi

/-- Both remaining pieces avoid the entire closed left side. -/
theorem Normalized.left_side_disjoint_remaining {d : SquareDissection}
    (h : Normalized d) {i : Fin 4} (hi : i = 2 ∨ i = 3) :
    Disjoint (segment ℝ (corner 0) (corner 3)) (d.piece i) := by
  apply Set.disjoint_left.mpr
  intro x hx hxi
  have h1i : (1 : Fin 4) ≠ i := by
    rcases hi with rfl | rfl <;> decide
  have hends : x ∉ ({corner 0, corner 3} : Set Plane) := by
    intro hxends
    rcases mem_insert_iff.mp hxends with rfl | hxthree
    · exact h.remaining_not_mem_corner hi (by decide : (0 : Fin 4) ≠ 2) hxi
    · obtain rfl := mem_singleton_iff.mp hxthree
      exact h.remaining_not_mem_corner hi (by decide : (3 : Fin 4) ≠ 2) hxi
  exact left_open_not_mem_of_left_segment d h1i h.bottom_left_sides.2
    ⟨hx, hends⟩ hxi

/-- Every actual point of either remaining piece is strictly above the
bottom side and strictly to the right of the left side. -/
theorem Normalized.remaining_coordinates_pos {d : SquareDissection}
    (h : Normalized d) {i : Fin 4} (hi : i = 2 ∨ i = 3) {x : Plane}
    (hx : x ∈ d.piece i) : 0 < x 0 ∧ 0 < x 1 := by
  have hxS := d.piece_subset i hx
  constructor
  · apply lt_of_le_of_ne hxS.1.1
    intro heq
    have hxleft : x ∈ segment ℝ (corner 0) (corner 3) :=
      left_segment_coordinates.mpr ⟨heq.symm, hxS.2⟩
    exact Set.disjoint_left.mp (h.left_side_disjoint_remaining hi) hxleft hx
  · apply lt_of_le_of_ne hxS.2.1
    intro heq
    have hxbottom : x ∈ segment ℝ (corner 0) (corner 1) :=
      bottom_segment_coordinates.mpr ⟨heq.symm, hxS.1⟩
    exact Set.disjoint_left.mp (h.bottom_side_disjoint_remaining hi) hxbottom hx

/-- Strict coordinate bounds for the singleton-corner piece. -/
theorem Normalized.piece_two_coordinates_pos {d : SquareDissection}
    (h : Normalized d) {x : Plane} (hx : x ∈ d.piece 2) :
    0 < x 0 ∧ 0 < x 1 :=
  h.remaining_coordinates_pos (Or.inl rfl) hx

/-- Strict coordinate bounds for the corner-free piece. -/
theorem Normalized.piece_three_coordinates_pos {d : SquareDissection}
    (h : Normalized d) {x : Plane} (hx : x ∈ d.piece 3) :
    0 < x 0 ∧ 0 < x 1 :=
  h.remaining_coordinates_pos (Or.inr rfl) hx

end Puzzling139335.N5

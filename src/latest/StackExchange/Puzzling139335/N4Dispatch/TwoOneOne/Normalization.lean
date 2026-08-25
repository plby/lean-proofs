import StackExchange.Puzzling139335.N5.TwoCorner
import StackExchange.Puzzling139335.N5.Transport
import StackExchange.Puzzling139335.N7.RepeatedSide
import StackExchange.Puzzling139335.FourIncidences

/-!
# Normalizing the actual degree-(2,1,1,0) corner pattern

The piece with two corners is moved to the bottom side by a symmetry of
the entire square. The singleton labels are then interchanged if needed.
All corner memberships and all counts below refer to the actual pieces.
-/

open Set

namespace Puzzling139335.N4Dispatch.TwoOneOne

/-- The actual normalized corner pattern, before identifying the
congruence between the two singleton pieces. -/
structure CornerPattern (d : SquareDissection) : Prop where
  count_zero : d.tileCornerCount 0 = 2
  count_one : d.tileCornerCount 1 = 1
  count_two : d.tileCornerCount 2 = 1
  count_three : d.tileCornerCount 3 = 0
  bottom_left : corner 0 ∈ d.piece 0
  bottom_right : corner 1 ∈ d.piece 0
  top_right : corner 2 ∈ d.piece 1
  top_left : corner 3 ∈ d.piece 2

theorem four_incidences_of_counts (d : SquareDissection)
    (h0 : d.tileCornerCount 0 = 2) (h1 : d.tileCornerCount 1 = 1)
    (h2 : d.tileCornerCount 2 = 1) (h3 : d.tileCornerCount 3 = 0) :
    d.cornerIncidenceCount = 4 := by
  rw [d.cornerIncidenceCount_eq_sum_tileCornerCount,
    CornerCounting.sum_fin_four, h0, h1, h2, h3]

theorem CornerPattern.four_incidences {d : SquareDissection} (h : CornerPattern d) :
    d.cornerIncidenceCount = 4 :=
  four_incidences_of_counts d h.count_zero h.count_one h.count_two h.count_three

/-- The diameter obstruction makes a two-corner piece an actual side pair. -/
theorem exists_side_of_count_two (d : SquareDissection) (hc : d.HasProtectedCenter)
    (i : Fin 4) (hcount : d.tileCornerCount i = 2) :
    ∃ a : Fin 4, corner a ∈ d.piece i ∧ corner (a + 1) ∈ d.piece i := by
  obtain ⟨a, b, hab, hcorners⟩ := N5.two_corners_of_count_two d i hcount
  have ha := (hcorners a).mpr (Or.inl rfl)
  have hb := (hcorners b).mpr (Or.inr rfl)
  have hbo : b ≠ a + 2 := by
    intro heq
    exact d.no_opposite_corners hc i a ⟨ha, heq ▸ hb⟩
  have hadj : b = a + 1 ∨ b = a + 3 := by
    fin_cases a <;> fin_cases b <;> simp_all
  rcases hadj with rfl | rfl
  · exact ⟨a, ha, hb⟩
  · refine ⟨a + 3, hb, ?_⟩
    have heq : a + 3 + 1 = a := by fin_cases a <;> decide
    rwa [heq]

theorem corner_index_eq_of_count_one (d : SquareDissection) {i a b : Fin 4}
    (hcount : d.tileCornerCount i = 1)
    (ha : corner a ∈ d.piece i) (hb : corner b ∈ d.piece i) : a = b := by
  obtain ⟨c, _, huniq⟩ := N5.unique_corner_of_tile_count_one d i hcount
  exact (huniq a ha).trans (huniq b hb).symm

/-- Once the double piece is at the bottom, the other two corners are
owned by the two singleton pieces in one of the two possible orders. -/
theorem upper_singleton_orders (d : SquareDissection) (hc : d.HasProtectedCenter)
    (h1 : d.tileCornerCount 1 = 1) (h2 : d.tileCornerCount 2 = 1)
    (h3 : d.tileCornerCount 3 = 0)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0) :
    (corner 2 ∈ d.piece 1 ∧ corner 3 ∈ d.piece 2) ∨
      (corner 2 ∈ d.piece 2 ∧ corner 3 ∈ d.piece 1) := by
  have hnot0 : corner 2 ∉ d.piece 0 := by
    intro h
    exact d.no_opposite_corners hc 0 0 ⟨hBL, h⟩
  have hnot1 : corner 3 ∉ d.piece 0 := by
    intro h
    exact d.no_opposite_corners hc 0 1 ⟨hBR, h⟩
  have hright : corner 2 ∈ d.piece 1 ∨ corner 2 ∈ d.piece 2 := by
    obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare 2)
    fin_cases i
    · exact (hnot0 hi).elim
    · exact Or.inl hi
    · exact Or.inr hi
    · exact (N5.no_corner_of_count_zero d 3 h3 2 hi).elim
  have hleft : corner 3 ∈ d.piece 1 ∨ corner 3 ∈ d.piece 2 := by
    obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare 3)
    fin_cases i
    · exact (hnot1 hi).elim
    · exact Or.inl hi
    · exact Or.inr hi
    · exact (N5.no_corner_of_count_zero d 3 h3 3 hi).elim
  rcases hright with hr | hr <;> rcases hleft with hl | hl
  · have heq := corner_index_eq_of_count_one d h1 hr hl
    exact (by decide : (2 : Fin 4) ≠ 3) heq |>.elim
  · exact Or.inl ⟨hr, hl⟩
  · exact Or.inr ⟨hr, hl⟩
  · have heq := corner_index_eq_of_count_one d h2 hr hl
    exact (by decide : (2 : Fin 4) ≠ 3) heq |>.elim

/-- A common square symmetry and, at most, an interchange of the two
singleton labels produces the normalized actual corner pattern. -/
theorem exists_cornerPattern_of_degree2110 (d : SquareDissection)
    (hc : d.HasProtectedCenter)
    (h0 : d.tileCornerCount 0 = 2) (h1 : d.tileCornerCount 1 = 1)
    (h2 : d.tileCornerCount 2 = 1) (h3 : d.tileCornerCount 3 = 0) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ CornerPattern D := by
  obtain ⟨a, ha, hb⟩ := exists_side_of_count_two d hc 0 h0
  let f := N7.sideFrame a
  have hf : f '' unitSquare = unitSquare := N7.sideFrame_image_square a
  let D := d.map f hf
  have hD : D.HasProtectedCenter := (d.map_hasProtectedCenter f hf).mpr hc
  have hD0 : D.tileCornerCount 0 = 2 :=
    (N5.tileCornerCount_map d f hf 0).trans h0
  have hD1 : D.tileCornerCount 1 = 1 :=
    (N5.tileCornerCount_map d f hf 1).trans h1
  have hD2 : D.tileCornerCount 2 = 1 :=
    (N5.tileCornerCount_map d f hf 2).trans h2
  have hD3 : D.tileCornerCount 3 = 0 :=
    (N5.tileCornerCount_map d f hf 3).trans h3
  have hBL : corner 0 ∈ D.piece 0 :=
    ⟨corner a, ha, N7.sideFrame_first a⟩
  have hBR : corner 1 ∈ D.piece 0 :=
    ⟨corner (a + 1), hb, N7.sideFrame_second a⟩
  rcases upper_singleton_orders D hD hD1 hD2 hD3 hBL hBR with horder | horder
  · exact ⟨D, hD, hD0, hD1, hD2, hD3, hBL, hBR, horder.1, horder.2⟩
  · let E := D.reindex (Equiv.swap 1 2)
    have hE : E.HasProtectedCenter := (D.reindex_hasProtectedCenter _).mpr hD
    refine ⟨E, hE, ?_⟩
    constructor
    · change D.tileCornerCount ((Equiv.swap 1 2) 0) = 2
      simpa [Equiv.swap_apply_def] using hD0
    · change D.tileCornerCount ((Equiv.swap 1 2) 1) = 1
      simpa using hD2
    · change D.tileCornerCount ((Equiv.swap 1 2) 2) = 1
      simpa using hD1
    · change D.tileCornerCount ((Equiv.swap 1 2) 3) = 0
      simpa [Equiv.swap_apply_def] using hD3
    · simpa [E, SquareDissection.reindex, Equiv.swap_apply_def] using hBL
    · simpa [E, SquareDissection.reindex, Equiv.swap_apply_def] using hBR
    · simpa [E, SquareDissection.reindex] using horder.1
    · simpa [E, SquareDissection.reindex] using horder.2

end Puzzling139335.N4Dispatch.TwoOneOne

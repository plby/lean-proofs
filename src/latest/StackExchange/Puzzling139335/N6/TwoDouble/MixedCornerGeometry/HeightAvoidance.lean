import StackExchange.Puzzling139335.N4OuterPair.Midline

/-!
# Height barriers for cornered middle pieces

These statements do not assume that the two middle pieces are cornerless.
The reflected outer pieces give the two half-square bounds; weighted mass
then makes every other piece cross the corresponding midline. The Jordan
height barriers exclude the open bottom and top sides.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.MixedCornerGeometry

noncomputable section

open ReflectionSeparation

theorem outer_halves (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1) :
    d.piece 0 ⊆ horizontalBand 0 (1 / 2) ∧
      d.piece 1 ⊆ horizontalBand (1 / 2) 1 := by
  have hhalf := d.horizontal_pair_halves_of_bottom_left
    (by decide : (0 : Fin 4) ≠ 1) hreflect hBL
  constructor
  · intro p hp
    exact ⟨(d.piece_subset 0 hp).1, (d.piece_subset 0 hp).2.1, hhalf.1 hp⟩
  · intro p hp
    exact ⟨(d.piece_subset 1 hp).1, hhalf.2 hp, (d.piece_subset 1 hp).2.2⟩

theorem other_above_midline (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    {i : Fin 4} (hi : i ≠ 0) :
    ∃ p ∈ interior (d.piece i), (1 / 2 : ℝ) < p 1 := by
  obtain ⟨c, hcenter⟩ := hc
  have hc0 : c ≠ 0 := by
    intro heq
    subst c
    exact (d.center_not_mem_fixed_pair (by decide : (0 : Fin 4) ≠ 1)
      horizontal hreflect horizontal_center).1 hcenter
  by_cases hic : i = c
  · subst i
    exact (d.center_piece_crosses_midline hcenter).2
  · exact d.exists_interior_above_of_lower_piece hcenter hc0 (Ne.symm hic) hi.symm
      (outer_halves d hBL hreflect).1

theorem other_below_midline (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    {i : Fin 4} (hi : i ≠ 1) :
    ∃ p ∈ interior (d.piece i), p 1 < (1 / 2 : ℝ) := by
  obtain ⟨c, hcenter⟩ := hc
  have hc1 : c ≠ 1 := by
    intro heq
    subst c
    exact (d.center_not_mem_fixed_pair (by decide : (0 : Fin 4) ≠ 1)
      horizontal hreflect horizontal_center).2 hcenter
  by_cases hic : i = c
  · subst i
    exact (d.center_piece_crosses_midline hcenter).1
  · exact d.exists_interior_below_of_upper_piece hcenter hc1 (Ne.symm hic) hi.symm
      (outer_halves d hBL hreflect).2

theorem top_left_mem (d : SquareDissection) (hBL : corner 0 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1) : corner 3 ∈ d.piece 1 := by
  rw [← hreflect]
  refine ⟨corner 0, hBL, ?_⟩
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

theorem top_right_mem (d : SquareDissection) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1) : corner 2 ∈ d.piece 1 := by
  rw [← hreflect]
  refine ⟨corner 1, hBR, ?_⟩
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

/-- A non-bottom piece missing the bottom-left corner can touch the bottom
line only at the bottom-right corner. -/
theorem bottom_contact_eq_right (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    {i : Fin 4} (hi : i ≠ 0) (hnotBL : corner 0 ∉ d.piece i)
    {p : Plane} (hp : p ∈ d.piece i) (hy : p 1 = 0) : p = corner 1 := by
  have hpS := d.piece_subset i hp
  by_cases hx1 : p 0 = 1
  · ext k
    fin_cases k <;> simp [corner, hx1, hy]
  have hx0 : p 0 ≠ 0 := by
    intro hx0
    have hp0 : p = corner 0 := by
      ext k
      fin_cases k <;> simp [corner, hx0, hy]
    exact hnotBL (hp0 ▸ hp)
  have hpeq : p = Schoenflies.Plane.mk (p 0) 0 := by
    ext k
    fin_cases k
    · rfl
    · exact hy
  obtain ⟨q, hq, hqy⟩ := other_above_midline d hc hBL hreflect hi
  exact (RectangularHull.bottom_contact_above_height_impossible
    (d.jordan 0) (d.jordan i) (d.piece_subset 0) (d.piece_subset i)
    (d.disjoint_interiors hi.symm)
    (by simpa [corner, Schoenflies.Plane.mk] using hBL)
    (by simpa [corner, Schoenflies.Plane.mk] using hBR)
    (fun p hp => ((outer_halves d hBL hreflect).1 hp).2.2)
    ⟨q, interior_subset hq, hqy⟩
    (lt_of_le_of_ne hpS.1.1 hx0.symm) (lt_of_le_of_ne hpS.1.2 hx1)
    (hpeq ▸ hp)).elim

/-- A non-top piece missing the top-left corner can touch the top line
only at the top-right corner. -/
theorem top_contact_eq_right (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    {i : Fin 4} (hi : i ≠ 1) (hnotTL : corner 3 ∉ d.piece i)
    {p : Plane} (hp : p ∈ d.piece i) (hy : p 1 = 1) : p = corner 2 := by
  have hpS := d.piece_subset i hp
  by_cases hx1 : p 0 = 1
  · ext k
    fin_cases k <;> simp [corner, hx1, hy]
  have hx0 : p 0 ≠ 0 := by
    intro hx0
    have hp0 : p = corner 3 := by
      ext k
      fin_cases k <;> simp [corner, hx0, hy]
    exact hnotTL (hp0 ▸ hp)
  have hpeq : p = Schoenflies.Plane.mk (p 0) 1 := by
    ext k
    fin_cases k
    · rfl
    · exact hy
  obtain ⟨q, hq, hqy⟩ := other_below_midline d hc hBL hreflect hi
  exact (RectangularHull.top_contact_below_height_impossible
    (d.jordan 1) (d.jordan i) (d.piece_subset 1) (d.piece_subset i)
    (d.disjoint_interiors hi.symm)
    (by simpa [corner, Schoenflies.Plane.mk] using top_left_mem d hBL hreflect)
    (by simpa [corner, Schoenflies.Plane.mk] using top_right_mem d hBR hreflect)
    (fun p hp => ((outer_halves d hBL hreflect).2 hp).2.1)
    ⟨q, interior_subset hq, hqy⟩
    (lt_of_le_of_ne hpS.1.1 hx0.symm) (lt_of_le_of_ne hpS.1.2 hx1)
    (hpeq ▸ hp)).elim

end

end Puzzling139335.N6.TwoDouble.MixedCornerGeometry

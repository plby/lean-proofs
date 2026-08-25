import StackExchange.Puzzling139335.N6.TripleEqualParity.Diameter
import StackExchange.Puzzling139335.N6.TripleEqualParity.SideForcing.ClosedCover

/-!
# Boundary points forced into the fourth piece

The first three normalized placements miss the upper tails of the right
and top sides of the square. Coverage assigns those tails to the fourth
piece, and closedness includes their lower endpoints. The conclusion is
membership in the actual piece, not only in its convex hull.
-/

open Set
open Puzzling139335.N6.TripleSectors

namespace Puzzling139335.N6.TripleEqualParity

noncomputable section

/-- On the right side, the three known placements cannot extend above
the exact height `2 - sqrt 3`. -/
theorem other_right_side_height (d : SquareDissection)
    (h0 : d.piece 0 ⊆ equalParityBound)
    (h1 : d.piece 1 ⊆ rotateThirty '' equalParityBound)
    (h2 : d.piece 2 ⊆ rotateSixty '' equalParityBound)
    {i : Fin 4} (hi : i ≠ 3) {y : ℝ} (hy : point 1 y ∈ d.piece i) :
    y ≤ t := by
  fin_cases i
  · exact equalParityBound_right_height (h0 hy) rfl
  · obtain ⟨p, hp, heq⟩ := h1 hy
    have hx : rotateThirty p 0 = 1 := congrArg (fun q : Plane => q 0) heq
    have hlt := rotateThirty_first_lt_one (equalParityBound_subset_thirtyCone hp)
    exact False.elim ((ne_of_lt hlt) hx)
  · obtain ⟨p, hp, heq⟩ := h2 hy
    have hx : rotateSixty p 0 = 1 := congrArg (fun q : Plane => q 0) heq
    exact False.elim ((ne_of_lt (rotateSixty_first_lt_one hp)) hx)
  · exact False.elim (hi rfl)

/-- The corresponding upper bound on the top side. -/
theorem other_top_side_coordinate (d : SquareDissection)
    (h0 : d.piece 0 ⊆ equalParityBound)
    (h1 : d.piece 1 ⊆ rotateThirty '' equalParityBound)
    (h2 : d.piece 2 ⊆ rotateSixty '' equalParityBound)
    {i : Fin 4} (hi : i ≠ 3) {x : ℝ} (hx : point x 1 ∈ d.piece i) :
    x ≤ t := by
  fin_cases i
  · have hheight := equalParityBound_second_le_half (h0 hx)
    change (1 : ℝ) ≤ 1 / 2 at hheight
    norm_num at hheight
  · obtain ⟨p, hp, heq⟩ := h1 hx
    have hy : rotateThirty p 1 = 1 := congrArg (fun q : Plane => q 1) heq
    exact False.elim ((ne_of_lt (rotateThirty_second_lt_one hp)) hy)
  · obtain ⟨p, hp, heq⟩ := h2 hx
    have hy : rotateSixty p 1 = 1 := congrArg (fun q : Plane => q 1) heq
    have hp0 : rotateSixty p 0 = x := congrArg (fun q : Plane => q 0) heq
    have hbound := rotateSixty_top_coordinate hp hy
    rw [hp0] at hbound
    exact hbound
  · exact False.elim (hi rfl)

/-- The normalized configuration forces all three vertices of the named
right isosceles triangle into the actual fourth piece. -/
theorem forced_corner_triangle_mem (d : SquareDissection)
    (h0 : d.piece 0 ⊆ equalParityBound)
    (h1 : d.piece 1 ⊆ rotateThirty '' equalParityBound)
    (h2 : d.piece 2 ⊆ rotateSixty '' equalParityBound) :
    point 1 t ∈ d.piece 3 ∧ point 1 1 ∈ d.piece 3 ∧ point t 1 ∈ d.piece 3 := by
  have hright : ∀ y ∈ Icc t 1, point 1 y ∈ d.piece 3 := by
    apply closed_piece_owns_side_tail d 3 (fun y => point 1 y)
      (by unfold point; fun_prop) t_pos.le t_lt_one
    · intro y hy
      exact ⟨⟨by norm_num, le_rfl⟩, hy⟩
    · intro i hi y _ hy
      exact other_right_side_height d h0 h1 h2 hi hy
  have htop : ∀ x ∈ Icc t 1, point x 1 ∈ d.piece 3 := by
    apply closed_piece_owns_side_tail d 3 (fun x => point x 1)
      (by unfold point; fun_prop) t_pos.le t_lt_one
    · intro x hx
      exact ⟨hx, ⟨by norm_num, le_rfl⟩⟩
    · intro i hi x _ hx
      exact other_top_side_coordinate d h0 h1 h2 hi hx
  exact ⟨hright t ⟨le_rfl, t_lt_one.le⟩,
    hright 1 ⟨t_lt_one.le, le_rfl⟩, htop t ⟨le_rfl, t_lt_one.le⟩⟩

end

end Puzzling139335.N6.TripleEqualParity

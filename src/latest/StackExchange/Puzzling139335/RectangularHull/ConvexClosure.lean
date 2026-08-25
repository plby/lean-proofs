import StackExchange.Puzzling139335.RectangularHull.AxisBox
import StackExchange.Puzzling139335.JordanRegion

/-!
# Closing the isolated rectangular-band alternative

Once a single piece is an actual rectangle, congruence makes every piece
convex. A cornerless unit-width rectangle of height one quarter supported
at a quarter height then has the square center on its opposite side.
-/

open Set

namespace Puzzling139335

theorem SquareDissection.piece_convex_of_one (d : SquareDissection) {i : Fin 4}
    (hi : Convex ℝ (d.piece i)) (j : Fin 4) : Convex ℝ (d.piece j) := by
  obtain ⟨e, he⟩ := d.congruent i j
  rw [← he]
  exact hi.affine_image e.toAffineEquiv.toAffineMap

theorem SquareDissection.not_protectedCenter_of_center_mem_frontier (d : SquareDissection)
    {i : Fin 4} (hi : squareCenter ∈ frontier (d.piece i)) : ¬ d.HasProtectedCenter := by
  rintro ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    exact hi.2 hj
  · exact d.not_mem_other_piece hji hj ((d.jordan i).isClosed.frontier_subset hi)

namespace RectangularHull

theorem quarter_rectangle_center_mem_frontier {b t y : ℝ}
    (hheight : t - b = 1 / 4)
    (hBL : (!₂[0, 0] : Plane) ∉ closedAxisBox 0 1 b t)
    (hTL : (!₂[0, 1] : Plane) ∉ closedAxisBox 0 1 b t)
    (hy : y = 1 / 4 ∨ y = 3 / 4)
    (hfront : (!₂[1 / 2, y] : Plane) ∈ frontier (closedAxisBox 0 1 b t)) :
    squareCenter ∈ frontier (closedAxisBox 0 1 b t) := by
  have hmem := (isClosed_closedAxisBox 0 1 b t).frontier_subset hfront
  have hby : b ≤ y := hmem.2.1
  have hyt : y ≤ t := hmem.2.2
  have hedge : y = b ∨ y = t := by
    by_cases hyb : y = b
    · exact Or.inl hyb
    · right
      by_contra hyt'
      apply hfront.2
      apply mem_interior_closedAxisBox.mpr
      exact ⟨by norm_num, by norm_num, lt_of_le_of_ne hby (Ne.symm hyb),
        lt_of_le_of_ne hyt hyt'⟩
  have hends : (b = 1 / 4 ∧ t = 1 / 2) ∨ (b = 1 / 2 ∧ t = 3 / 4) := by
    rcases hy with hy | hy <;> rcases hedge with hedge | hedge
    · left
      constructor <;> linarith
    · exfalso
      apply hBL
      change (0 ≤ (0 : ℝ) ∧ 0 ≤ 1) ∧ b ≤ 0 ∧ 0 ≤ t
      constructor
      · norm_num
      · constructor <;> linarith
    · exfalso
      apply hTL
      change (0 ≤ (0 : ℝ) ∧ 0 ≤ 1) ∧ b ≤ 1 ∧ 1 ≤ t
      constructor
      · norm_num
      · constructor <;> linarith
    · right
      constructor <;> linarith
  rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    rw [(isClosed_closedAxisBox _ _ _ _).frontier_eq]
    constructor
    · norm_num [closedAxisBox, squareCenter]
    · rw [mem_interior_closedAxisBox]
      norm_num [squareCenter]

theorem Frame.quarter_height_of_horizontal_span (R : Frame) (hAxis : R.AxisAligned)
    (hs : ‖R.second‖ = 1 / 4)
    (hS : R.carrier ⊆ unitSquare) {y : ℝ}
    (hleft : (!₂[0, y] : Plane) ∈ R.carrier)
    (hright : (!₂[1, y] : Plane) ∈ R.carrier) :
    R.boxLeft = 0 ∧ R.boxRight = 1 ∧ R.boxTop - R.boxBottom = 1 / 4 := by
  have ho := hS (R.vertices_subset_carrier R.origin_mem_vertices)
  have hd := hS (R.vertices_subset_carrier R.both_mem_vertices)
  have hl0 : 0 ≤ R.boxLeft := le_min ho.1.1 hd.1.1
  have hr1 : R.boxRight ≤ 1 := max_le ho.1.2 hd.1.2
  rw [R.carrier_eq_closedAxisBox hAxis] at hleft hright
  have hl : R.boxLeft = 0 := le_antisymm hleft.1.1 hl0
  have hr : R.boxRight = 1 := le_antisymm hr1 hright.1.2
  refine ⟨hl, hr, ?_⟩
  rcases R.axisBox_side_lengths hAxis with h | h
  · exact h.2.trans hs
  · exfalso
    rw [hl, hr, hs] at h
    norm_num at h

/-- This final geometric contradiction uses only an actual quarter-height
rectangle and the actual supporting unit segment of its placement. -/
theorem Frame.center_frontier_of_axis_quarter_rectangle (R : Frame)
    (hAxis : R.AxisAligned) (hs : ‖R.second‖ = 1 / 4)
    (hS : R.carrier ⊆ unitSquare) (hcornerless : ∀ j, corner j ∉ R.carrier)
    {y : ℝ} (hy : y = 1 / 4 ∨ y = 3 / 4)
    (hleft : (!₂[0, y] : Plane) ∈ R.carrier)
    (hright : (!₂[1, y] : Plane) ∈ R.carrier)
    (hfront : (!₂[1 / 2, y] : Plane) ∈ frontier R.carrier) :
    squareCenter ∈ frontier R.carrier := by
  obtain ⟨hl, hr, hh⟩ := R.quarter_height_of_horizontal_span hAxis hs hS hleft hright
  have hbox : R.carrier = closedAxisBox 0 1 R.boxBottom R.boxTop := by
    rw [R.carrier_eq_closedAxisBox hAxis, hl, hr]
  rw [hbox] at hfront ⊢
  apply quarter_rectangle_center_mem_frontier hh ?_ ?_ hy hfront
  · simpa [hbox, corner, Fin.ext_iff] using hcornerless 0
  · simpa [hbox, corner, Fin.ext_iff] using hcornerless 3

end RectangularHull

end Puzzling139335

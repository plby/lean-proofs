import StackExchange.Puzzling139335.RectangularHull.NormalizedBands
import StackExchange.Puzzling139335.RectangularHull.HorizontalSeparator
import StackExchange.Puzzling139335.RectangularHull.ConvexClosure
import StackExchange.Puzzling139335.BandMass.HorizontalSeparators

/-!
# Separator restrictions for the middle pieces

A middle piece cannot contain a full vertical unit segment: such a segment
would separate the two bottom corners of the bottom piece unless it were a
side of the square, in which case the middle piece would contain a corner.
A horizontal unit segment in a middle frontier has an integer quarter
height. Cornerlessness and the protected center exclude three of those five
heights.
-/

open Set

namespace Puzzling139335.RectangularHull

/-- A middle piece in the normalized configuration cannot span the square
vertically along a straight segment. -/
theorem middle_vertical_segment_impossible {d : SquareDissection} {h x : ℝ}
    {k : Fin 4} (N : NormalizedOuterBands d h) (hk : k = 2 ∨ k = 3)
    (hx : x ∈ Icc (0 : ℝ) 1)
    (hseg : segment ℝ (!₂[x, 0] : Plane) (!₂[x, 1] : Plane) ⊆ d.piece k) :
    False := by
  have h0k : (0 : Fin 4) ≠ k := by
    rcases hk with rfl | rfl <;> decide
  have hbottom := hseg (left_mem_segment ℝ (!₂[x, 0] : Plane) (!₂[x, 1] : Plane))
  rcases vertical_segment_separates_pieces d hseg h0k with hleft | hright
  · have h1 : 1 ≤ x := hleft _ N.bottom_corners.2
    have hx1 : x = 1 := le_antisymm hx.2 h1
    apply N.middle_cornerless k hk 1
    simpa [hx1, corner] using hbottom
  · have h0 : x ≤ 0 := hright _ N.bottom_corners.1
    have hx0 : x = 0 := le_antisymm h0 hx.1
    apply N.middle_cornerless k hk 0
    simpa [hx0, corner] using hbottom

/-- A full horizontal unit segment on a cornerless piece's frontier can
only occur at height one quarter or three quarters when the center is
protected. -/
theorem middle_horizontal_frontier_height_quarters (d : SquareDissection)
    (hc : d.HasProtectedCenter) {k : Fin 4} {y : ℝ}
    (hcornerless : ∀ j : Fin 4, corner j ∉ d.piece k)
    (hy : y ∈ Icc (0 : ℝ) 1)
    (hseg : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆
      frontier (d.piece k)) :
    y = 1 / 4 ∨ y = 3 / 4 := by
  have hfront : {p : Plane | p ∈ unitSquare ∧ p 1 = y} ⊆
      ⋃ i, frontier (d.piece i) := by
    rintro p ⟨hpS, hpy⟩
    apply mem_iUnion.mpr
    refine ⟨k, hseg ?_⟩
    rw [Schoenflies.mem_segment_horiz,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    exact ⟨hpy, hpS.1⟩
  obtain ⟨n, hn, hheight⟩ :=
    d.horizontal_frontier_separator_height_eq_nat_quarter hy hfront
  have hleft := (d.jordan k).isClosed.frontier_subset
    (hseg (left_mem_segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane)))
  interval_cases n
  · norm_num at hheight
    exfalso
    apply hcornerless 0
    simpa [hheight, corner] using hleft
  · left
    simpa using hheight
  · norm_num at hheight
    exfalso
    apply d.not_protectedCenter_of_center_mem_frontier (i := k) ?_ hc
    apply hseg
    rw [Schoenflies.mem_segment_horiz,
      segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    norm_num [squareCenter, hheight]
  · right
    simpa using hheight
  · norm_num at hheight
    exfalso
    apply hcornerless 3
    simpa [hheight, corner] using hleft

end Puzzling139335.RectangularHull

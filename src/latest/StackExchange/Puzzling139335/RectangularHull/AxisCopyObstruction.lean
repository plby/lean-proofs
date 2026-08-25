import StackExchange.Puzzling139335.RectangularHull.AxisCopyObstruction.SeparatorHeights
import StackExchange.Puzzling139335.RectangularHull.AxisCopyObstruction.QuarterBand
import StackExchange.Puzzling139335.RectangularHull.AxisCopyObstruction.FrameClosure
import StackExchange.Puzzling139335.RectangularHull.AxisSegment

/-!
# An axis-aligned copy cannot be a middle piece

The genuine unit base of the normalized bottom piece maps to a full horizontal
or vertical segment.  The vertical alternative contradicts cornerlessness.
The horizontal alternative isolates a quarter band, forces convexity of every
piece, and places the square center on the boundary of the actual copied
quarter rectangle.
-/

open Set Puzzling139335.PlaneIsometries

namespace Puzzling139335.RectangularHull

/-- A middle copy supported by a horizontal quarter-height segment is an
actual rectangle whose boundary contains the center. -/
theorem normalized_middle_horizontal_axis_impossible
    {d : SquareDissection} {h y : ℝ} {k : Fin 4}
    (N : NormalizedOuterBands d h) (hc : d.HasProtectedCenter) (hk : k = 2 ∨ k = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece k)
    (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0)
    (hy : y = 1 / 4 ∨ y = 3 / 4)
    (hfront : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆
      frontier (d.piece k)) : False := by
  have hsegment : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆ d.piece k :=
    hfront.trans (d.jordan k).isClosed.frontier_subset
  obtain ⟨hh, hconv⟩ := quarter_horizontal_segment_forces_height_and_convex N hk hy hsegment
  exact d.not_protectedCenter_of_center_mem_frontier
    (normalized_axis_quarter_copy_center_frontier N hk e he hAxis hh (hconv k) hy hfront) hc

/-- Neither orientation of an axis-aligned congruent copy can realize one of
the two cornerless middle pieces in a protected-center dissection. -/
theorem normalized_axis_copy_impossible
    {d : SquareDissection} {h : ℝ} {k : Fin 4}
    (N : NormalizedOuterBands d h) (hc : d.HasProtectedCenter) (hk : k = 2 ∨ k = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece k)
    (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0) : False := by
  have he0 : e (!₂[0, 0] : Plane) ∈ unitSquare := by
    apply d.piece_subset k
    rw [← he]
    exact mem_image_of_mem e N.bottom_corners.1
  have he1 : e (!₂[1, 0] : Plane) ∈ unitSquare := by
    apply d.piece_subset k
    rw [← he]
    exact mem_image_of_mem e N.bottom_corners.2
  have hbase := N.isometry_base_frontier hc e he
  rcases affine_unit_base_image_axis_segment_of_row_axis e he0 he1 hAxis with
    ⟨x, hx, hvertical⟩ | ⟨y, hy, hhorizontal⟩
  · have hfront : segment ℝ (!₂[x, 0] : Plane) (!₂[x, 1] : Plane) ⊆
        frontier (d.piece k) := hvertical ▸ hbase
    exact middle_vertical_segment_impossible N hk hx
      (hfront.trans (d.jordan k).isClosed.frontier_subset)
  · have hfront : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆
        frontier (d.piece k) := hhorizontal ▸ hbase
    have hyquarter := middle_horizontal_frontier_height_quarters d hc
      (N.middle_cornerless k hk) hy hfront
    exact normalized_middle_horizontal_axis_impossible N hc hk e he hAxis hyquarter hfront

end Puzzling139335.RectangularHull

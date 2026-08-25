import StackExchange.Puzzling139335.RectangularHull.NormalizedBands
import StackExchange.Puzzling139335.RectangularHull.CanonicalFrame
import StackExchange.Puzzling139335.RectangularHull.ConvexClosure

/-! # The center on an actual axis-aligned quarter copy -/

open Set Puzzling139335.PlaneIsometries

namespace Puzzling139335.RectangularHull

/-- Once the normalized height is a quarter and the target piece is convex,
its isometric rectangle frame is the actual piece.  A horizontal frontier
segment at a quarter height then puts the square center on its frontier. -/
theorem normalized_axis_quarter_copy_center_frontier
    {d : SquareDissection} {h y : ℝ} {k : Fin 4}
    (N : NormalizedOuterBands d h) (hk : k = 2 ∨ k = 3)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece k)
    (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0)
    (hh : h = 1 / 4) (hconv : Convex ℝ (d.piece k))
    (hy : y = 1 / 4 ∨ y = 3 / 4)
    (hfront : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆
      frontier (d.piece k)) : squareCenter ∈ frontier (d.piece k) := by
  have hsegment : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆ d.piece k :=
    hfront.trans (d.jordan k).isClosed.frontier_subset
  let R : Frame := (unitFrame N.height_pos).map e
  have hR : R.carrier = d.piece k := by
    calc
      R.carrier = e '' axisBox h := mapped_unitFrame_carrier e N.height_pos
      _ = convexHull ℝ (d.piece k) := N.isometry_hull_image e he
      _ = d.piece k := hconv.convexHull_eq
  have hRaxis : R.AxisAligned := mapped_unitFrame_axisAligned e N.height_pos hAxis
  have hRheight : ‖R.second‖ = 1 / 4 :=
    (mapped_unitFrame_norm_second e N.height_pos).trans hh
  have hRS : R.carrier ⊆ unitSquare := by
    rw [hR]
    exact d.piece_subset k
  have hRcornerless : ∀ j, corner j ∉ R.carrier := by
    simpa only [hR] using N.middle_cornerless k hk
  have hRsegment : segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) ⊆ R.carrier := by
    rw [hR]
    exact hsegment
  have hmid : (!₂[1 / 2, y] : Plane) ∈
      segment ℝ (!₂[0, y] : Plane) (!₂[1, y] : Plane) := by
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    norm_num
  have hRfront : (!₂[1 / 2, y] : Plane) ∈ frontier R.carrier := by
    rw [hR]
    exact hfront hmid
  have hcenter := R.center_frontier_of_axis_quarter_rectangle hRaxis hRheight hRS
    hRcornerless hy (hRsegment (left_mem_segment ℝ _ _))
    (hRsegment (right_mem_segment ℝ _ _)) hRfront
  simpa only [hR] using hcenter

end Puzzling139335.RectangularHull

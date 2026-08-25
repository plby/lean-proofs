import StackExchange.Puzzling139335.RectangularHull.DimensionReduction
import StackExchange.Puzzling139335.RectangularHull.Normalization
import StackExchange.Puzzling139335.RectangularHull.AxisCopyExistence
import StackExchange.Puzzling139335.RectangularHull.AxisCopyObstruction

/-!
# Rectangular convex hulls cannot protect the center

This is the complete rectangular-hull case for four congruent closed
Jordan regions. Their boundaries need not be polygonal or rectifiable.
The only additional geometric hypothesis is that one piece has a
nondegenerate rectangular convex hull; congruence supplies the other hulls.

The proof derives common frames, excludes two edge lengths below one,
normalizes the remaining opposite outer bands, and proves that a middle
copy has an axis-aligned supporting unit segment. The final separator
argument uses the actual piece frontiers and their weighted quarter masses.
No axis-preserving placement or convexity theorem is assumed.
-/

namespace Puzzling139335

open RectangularHull

/-- A rectangular convex hull is impossible in a protected-center square
dissection, irrespective of the orientations of the four congruences. -/
theorem SquareDissection.not_protectedCenter_of_rectangular_hull
    (d : SquareDissection) {i : Fin 4} (hHull : HasRectangularHull (d.piece i)) :
    ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨F⟩ := exists_commonFrames d hHull
  obtain ⟨G, h, hh0, hh1, hfirst, hsecond⟩ := exists_unit_edge_frames F hc
  obtain ⟨d', N, hc'⟩ := G.exists_normalized_outerBands hc hh0 hh1 hfirst hsecond
  obtain ⟨k, hk, e, he, hAxis⟩ := N.exists_axis_middle_copy
  exact normalized_axis_copy_impossible N hc' hk e he hAxis

theorem SquareDissection.no_rectangular_hull (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) : ¬ HasRectangularHull (d.piece i) := by
  intro hHull
  exact d.not_protectedCenter_of_rectangular_hull hHull hc

end Puzzling139335

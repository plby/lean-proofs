import StackExchange.Puzzling139335.UnitPairs.SideSupport
import StackExchange.Puzzling139335.UnitPairs.TriangleHull
import StackExchange.Puzzling139335.UnitPairs.RightCorner

/-!
# Intrinsic unit pairs with actual square placements

Three points whose three unit pairs can each be placed on a side of the
square determine the convex hull of the entire piece.  The actual
placements produce the supporting halfplanes; equilateral distances
ensure that those halfplanes enclose a nondegenerate triangle.
-/

open Set

namespace Puzzling139335.UnitPairs

/-- Three actual unit-side placements force every point of the set into
the triangle of their endpoints.  No convexity or boundary regularity of
the set is assumed. -/
theorem subset_convexHull_of_three_unitSidePairs {P : Set Plane} {a b c : Plane}
    (hab : IsUnitSidePair P a b) (hbc : IsUnitSidePair P b c)
    (hca : IsUnitSidePair P c a) :
    P ⊆ convexHull ℝ ({a, b, c} : Set Plane) := by
  intro x hx
  exact mem_convexHull_triangle_of_sideDet
    (sideDet_ne_zero_of_equidistant hab.2.2.1 hbc.2.2.1 hca.2.2.1)
    (hab.sideDet_mul_nonneg hbc.2.1 hx)
    (hbc.sideDet_mul_nonneg hab.1 hx)
    (hca.sideDet_mul_nonneg hab.2.1 hx)

/-- The equilateral triangle formed by three mutually used unit side pairs
is exactly the convex hull of the original set. -/
theorem convexHull_eq_of_three_unitSidePairs {P : Set Plane} {a b c : Plane}
    (hab : IsUnitSidePair P a b) (hbc : IsUnitSidePair P b c)
    (hca : IsUnitSidePair P c a) :
    convexHull ℝ P = convexHull ℝ ({a, b, c} : Set Plane) := by
  apply Subset.antisymm
  · exact convexHull_min (subset_convexHull_of_three_unitSidePairs hab hbc hca)
      (convex_convexHull ℝ _)
  · apply convexHull_mono
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact hab.1
    · exact hab.2.1
    · exact hbc.2.1

end Puzzling139335.UnitPairs

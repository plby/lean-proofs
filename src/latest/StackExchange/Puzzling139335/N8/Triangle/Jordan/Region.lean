import StackExchange.Puzzling139335.N8.Triangle.Jordan.Convex
import StackExchange.Puzzling139335.N8.Triangle.Center

/-!
# A nondegenerate filled triangle is a Jordan region

Its centroid satisfies all three strict inward determinant inequalities,
so the compact convex hull has nonempty planar interior.
-/

open Set
open Puzzling139335.UnitPairs

namespace Puzzling139335.N8

private theorem sideDet_centroid (a b c : Plane) :
    sideDet a b ((1 / 3 : ℝ) • (a + b + c)) = sideDet a b c / 3 := by
  simp only [sideDet, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  ring

/-- The centroid of a nondegenerate triangle lies in its ordinary planar
interior. -/
theorem centroid_mem_interior_convexHull_triangle {a b c : Plane}
    (hnonzero : sideDet a b c ≠ 0) :
    (1 / 3 : ℝ) • (a + b + c) ∈
      interior (convexHull ℝ ({a, b, c} : Set Plane)) := by
  have hprod (u v w : Plane) (h : sideDet u v w ≠ 0) :
      0 < sideDet u v w * sideDet u v ((1 / 3 : ℝ) • (u + v + w)) := by
    rw [sideDet_centroid]
    nlinarith [sq_pos_of_ne_zero h]
  have hbc : sideDet b c a ≠ 0 := by
    rwa [sideDet_cyclic]
  have hca : sideDet c a b ≠ 0 := by
    rwa [sideDet_cyclic, sideDet_cyclic]
  apply mem_interior_convexHull_triangle_of_sideDet hnonzero
  · exact hprod a b c hnonzero
  · have hsum : a + b + c = b + c + a := by abel
    rw [hsum]
    exact hprod b c a hbc
  · have hsum : a + b + c = c + a + b := by abel
    rw [hsum]
    exact hprod c a b hca

/-- Every nondegenerate closed triangle is a Jordan region. -/
theorem isJordanRegion_convexHull_triangle {a b c : Plane}
    (hnonzero : sideDet a b c ≠ 0) :
    IsJordanRegion (convexHull ℝ ({a, b, c} : Set Plane)) := by
  apply isJordanRegion_of_isCompact_convex
  · exact (((finite_singleton c).insert b).insert a).isCompact_convexHull ℝ
  · exact convex_convexHull ℝ _
  · exact ⟨_, centroid_mem_interior_convexHull_triangle hnonzero⟩

end Puzzling139335.N8

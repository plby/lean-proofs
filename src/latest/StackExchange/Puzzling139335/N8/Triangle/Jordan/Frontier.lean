import StackExchange.Puzzling139335.N8.Triangle.Jordan.Region
import StackExchange.Puzzling139335.N8.Triangle.Jordan.Frontier.Algebra
import StackExchange.Puzzling139335.N8.Triangle.Jordan.Frontier.Support

/-!
# The exact boundary of a nondegenerate triangle

Strict inward determinants imply interior membership. Equality in any
one of them gives the corresponding actual side segment, and the
supporting line keeps that segment out of the interior.
-/

open Set
open Puzzling139335.UnitPairs

namespace Puzzling139335.N8

private theorem sideDet_eq_zero_of_mem_segment {a b x : Plane}
    (hx : x ∈ segment ℝ a b) : sideDet a b x = 0 := by
  obtain ⟨u, v, _, _, huv, rfl⟩ := hx
  rw [sideDet_smul_add a b a b huv]
  have ha : sideDet a b a = 0 := by simp [sideDet]
  have hb : sideDet a b b = 0 := by unfold sideDet; ring
  simp only [ha, hb, mul_zero, add_zero]

/-- Each actual side of a nondegenerate triangle lies on its frontier. -/
theorem segment_subset_frontier_convexHull_triangle {a b c : Plane}
    (hnonzero : sideDet a b c ≠ 0) :
    segment ℝ a b ⊆ frontier (convexHull ℝ ({a, b, c} : Set Plane)) := by
  intro x hx
  apply mem_frontier_of_sideDet_support hnonzero
    (fun y hy => sideDet_mul_nonneg_of_mem_convexHull_triangle hy)
    ?_ (sideDet_eq_zero_of_mem_segment hx)
  exact (convex_convexHull ℝ ({a, b, c} : Set Plane)).segment_subset
    (subset_convexHull ℝ _ (by simp))
    (subset_convexHull ℝ _ (by simp)) hx

/-- The frontier of a nondegenerate filled triangle is precisely the union
of its three closed side segments. -/
theorem frontier_convexHull_triangle {a b c : Plane}
    (hnonzero : sideDet a b c ≠ 0) :
    frontier (convexHull ℝ ({a, b, c} : Set Plane)) =
      segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  have hbc : sideDet b c a ≠ 0 := by rwa [sideDet_cyclic]
  have hca : sideDet c a b ≠ 0 := by rwa [sideDet_cyclic, sideDet_cyclic]
  ext x
  constructor
  · intro hx
    have hxT := (isClosed_convexHull_triangle a b c).frontier_subset hx
    have hxT' : x ∈ convexHull ℝ ({b, c, a} : Set Plane) := by
      rwa [convexHull_triangle_cyclic]
    have hxT'' : x ∈ convexHull ℝ ({c, a, b} : Set Plane) := by
      rwa [convexHull_triangle_cyclic]
    by_cases hab0 : sideDet a b x = 0
    · exact Or.inl (Or.inl
        (mem_segment_of_mem_convexHull_triangle_of_sideDet_eq_zero hnonzero hxT hab0))
    by_cases hbc0 : sideDet b c x = 0
    · exact Or.inl (Or.inr
        (mem_segment_of_mem_convexHull_triangle_of_sideDet_eq_zero hbc hxT' hbc0))
    by_cases hca0 : sideDet c a x = 0
    · exact Or.inr
        (mem_segment_of_mem_convexHull_triangle_of_sideDet_eq_zero hca hxT'' hca0)
    exfalso
    apply hx.2
    exact mem_interior_convexHull_triangle_of_sideDet hnonzero
      (lt_of_le_of_ne (sideDet_mul_nonneg_of_mem_convexHull_triangle hxT)
        (mul_ne_zero hnonzero hab0).symm)
      (lt_of_le_of_ne (sideDet_mul_nonneg_of_mem_convexHull_triangle hxT')
        (mul_ne_zero hbc hbc0).symm)
      (lt_of_le_of_ne (sideDet_mul_nonneg_of_mem_convexHull_triangle hxT'')
        (mul_ne_zero hca hca0).symm)
  · rintro ((hx | hx) | hx)
    · exact segment_subset_frontier_convexHull_triangle hnonzero hx
    · have h := segment_subset_frontier_convexHull_triangle hbc hx
      rwa [convexHull_triangle_cyclic] at h
    · have h := segment_subset_frontier_convexHull_triangle hca hx
      rwa [convexHull_triangle_cyclic, convexHull_triangle_cyclic] at h

theorem left_mem_frontier_convexHull_triangle {a b c : Plane}
    (hnonzero : sideDet a b c ≠ 0) :
    a ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane)) :=
  segment_subset_frontier_convexHull_triangle hnonzero (left_mem_segment ℝ a b)

theorem middle_mem_frontier_convexHull_triangle {a b c : Plane}
    (hnonzero : sideDet a b c ≠ 0) :
    b ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane)) :=
  segment_subset_frontier_convexHull_triangle hnonzero (right_mem_segment ℝ a b)

theorem right_mem_frontier_convexHull_triangle {a b c : Plane}
    (hnonzero : sideDet a b c ≠ 0) :
    c ∈ frontier (convexHull ℝ ({a, b, c} : Set Plane)) := by
  rw [frontier_convexHull_triangle hnonzero]
  exact Or.inl (Or.inr (right_mem_segment ℝ b c))

end Puzzling139335.N8

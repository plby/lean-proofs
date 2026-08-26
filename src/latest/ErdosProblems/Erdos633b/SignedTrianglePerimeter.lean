import ErdosProblems.Erdos633b.BoundaryAngleImages
import Mathlib.Analysis.InnerProductSpace.Convex

/-! Every signed perimeter with three unit signs is nonzero for a
nondegenerate triangle, by the strict triangle inequalities. -/

namespace Erdos633b.Triangle

theorem side_lt_add_sides (S : Triangle) (i : Fin 3) :
    S.side i < S.side (i + 1) + S.side (i + 2) := by
  have hne : dist (S.points (i + 1)) (S.points (i + 2)) ≠
      dist (S.points (i + 1)) (S.points i) + dist (S.points i) (S.points (i + 2)) := by
    intro he
    have hm : S.points i ∈ segment ℝ (S.points (i + 1)) (S.points (i + 2)) :=
      mem_segment_iff_wbtw.mpr (dist_add_dist_eq_iff.mp he.symm)
    have he' : S.points i ∈ S.edge i := by rwa [S.edge_eq_segment]
    exact S.ne_vertex_of_mem_edge i he' rfl
  have h := lt_of_le_of_ne (dist_triangle (S.points (i + 1)) (S.points i)
    (S.points (i + 2))) hne
  fin_cases i
  · change dist (S.points 1) (S.points 2) <
      dist (S.points 2) (S.points 0) + dist (S.points 0) (S.points 1)
    change dist (S.points 1) (S.points 2) <
      dist (S.points 1) (S.points 0) + dist (S.points 0) (S.points 2) at h
    simpa only [dist_comm (S.points 1) (S.points 0),
      dist_comm (S.points 0) (S.points 2), add_comm] using h
  · change dist (S.points 2) (S.points 0) <
      dist (S.points 0) (S.points 1) + dist (S.points 1) (S.points 2)
    change dist (S.points 2) (S.points 0) <
      dist (S.points 2) (S.points 1) + dist (S.points 1) (S.points 0) at h
    simpa only [dist_comm (S.points 2) (S.points 1),
      dist_comm (S.points 1) (S.points 0), add_comm] using h
  · change dist (S.points 0) (S.points 1) <
      dist (S.points 1) (S.points 2) + dist (S.points 2) (S.points 0)
    change dist (S.points 0) (S.points 1) <
      dist (S.points 0) (S.points 2) + dist (S.points 2) (S.points 1) at h
    simpa only [dist_comm (S.points 0) (S.points 2),
      dist_comm (S.points 2) (S.points 1), add_comm] using h

theorem signed_side_sum_ne_zero (S : Triangle) (ε : Fin 3 → ℤ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    (∑ i : Fin 3, (ε i : ℝ) * S.side i) ≠ 0 := by
  have h0 : S.side 0 < S.side 1 + S.side 2 := S.side_lt_add_sides 0
  have h1 : S.side 1 < S.side 2 + S.side 0 := S.side_lt_add_sides 1
  have h2 : S.side 2 < S.side 0 + S.side 1 := S.side_lt_add_sides 2
  rw [Fin.sum_univ_three]
  rcases hε 0 with h0' | h0' <;> rcases hε 1 with h1' | h1' <;>
    rcases hε 2 with h2' | h2' <;>
    simp only [h0', h1', h2', Int.cast_one, Int.cast_neg, one_mul, neg_mul] <;>
    nlinarith [S.side_pos 0, S.side_pos 1, S.side_pos 2]

end Erdos633b.Triangle

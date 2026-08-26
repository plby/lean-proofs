import ErdosProblems.Erdos633b.TriangleEdgeOrientation

/-! A tile edge contained in an outer edge has the same positive boundary
direction. The sign is forced by the actual inward barycentric half-plane. -/

namespace Erdos633b.Triangle

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem boundary_cyclicEdgeVectors_parallel (T S : Triangle) (i j : Fin 3)
    (he : S.edge j ⊆ T.edge i) :
    ∃ c : ℝ, S.cyclicEdgeVector j = c • T.cyclicEdgeVector i := by
  have hA := (he (S.edge_vertex_mem j (j + 1)
    ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))).2
  have hB := (he (S.edge_vertex_mem j (j + 2)
    ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j))).2
  refine ⟨T.coord (i + 2) (S.points (j + 2)) - T.coord (i + 2) (S.points (j + 1)), ?_⟩
  change S.points (j + 2) - S.points (j + 1) = _
  calc
    _ = (S.points (j + 2) - T.points (i + 1)) -
        (S.points (j + 1) - T.points (i + 1)) := by abel
    _ = _ := by
      rw [T.relative_edge_coordinates i (S.points (j + 2)),
        T.relative_edge_coordinates i (S.points (j + 1)), hA, hB]
      module

theorem boundary_positiveEdgeVectors_parallel (T S : Triangle)
    (o : Orientation ℝ Plane (Fin 2)) (i j : Fin 3) (he : S.edge j ⊆ T.edge i) :
    ∃ c : ℝ, S.positiveEdgeVector o j = c • T.positiveEdgeVector o i := by
  obtain ⟨c, hc⟩ := T.boundary_cyclicEdgeVectors_parallel S i j he
  unfold positiveEdgeVector
  split_ifs
  · exact ⟨c, hc⟩
  · refine ⟨-c, ?_⟩; rw [hc]; module
  · refine ⟨-c, ?_⟩; rw [hc]; module
  · refine ⟨c, ?_⟩; rw [hc]; module

theorem boundary_positiveEdgeVectors_same (T S : Triangle)
    (o : Orientation ℝ Plane (Fin 2)) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (he : S.edge j ⊆ T.edge i) :
    ∃ c : ℝ, 0 < c ∧ S.positiveEdgeVector o j = c • T.positiveEdgeVector o i := by
  obtain ⟨c, hc⟩ := T.boundary_positiveEdgeVectors_parallel S o i j he
  have hpS : S.coord j (S.points (j + 1)) = 0 := by
    rw [S.coord_vertex, if_neg ((by decide : ∀ j : Fin 3, j ≠ j + 1) j)]
  have hpT := (he (S.edge_vertex_mem j (j + 1)
    ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j))).2
  have hS := S.positiveEdgeVector_side_sign o j (S.points (j + 1)) (S.points j) hpS
  have hT := T.positiveEdgeVector_side_sign o i (S.points (j + 1)) (S.points j) hpT
  rw [S.coord_vertex, if_pos rfl, sign_one] at hS
  rw [sign_pos (T.coord_factor_pos_of_edge_subset S hST i j he)] at hT
  rw [hc, o.oangle_sign_smul_left, hT, mul_one] at hS
  exact ⟨c, sign_eq_one_iff.mp hS, hc⟩

theorem boundary_positiveEdgeDirections (T S : Triangle)
    (o : Orientation ℝ Plane (Fin 2)) (u : Plane) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (he : S.edge j ⊆ T.edge i) :
    S.positiveEdgeDirection o u j = T.positiveEdgeDirection o u i := by
  obtain ⟨c, hc, hv⟩ := T.boundary_positiveEdgeVectors_same S o hST i j he
  unfold positiveEdgeDirection
  rw [hv, o.oangle_smul_right_of_pos _ _ hc]

end Erdos633b.Triangle

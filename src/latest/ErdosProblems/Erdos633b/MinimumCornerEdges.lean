import ErdosProblems.Erdos633b.MinimumCorner
import ErdosProblems.Erdos633b.BoundaryLength

/-! The unique tile at a minimum corner contributes complete sides to both
adjacent outer sides. The proof uses extreme endpoints and radial reconstruction. -/

namespace Erdos633b

namespace Triangle

theorem cornerProject_pair_of_section_eq (T S : Triangle) (i j : Fin 3)
    (he : T.cornerSection S i j = T.edge i) :
    (T.cornerProject i (S.points (j + 1)) = T.points (i + 1) ∧
      T.cornerProject i (S.points (j + 2)) = T.points (i + 2)) ∨
    (T.cornerProject i (S.points (j + 1)) = T.points (i + 2) ∧
      T.cornerProject i (S.points (j + 2)) = T.points (i + 1)) := by
  let A := T.cornerProject i (S.points (j + 1))
  let B := T.cornerProject i (S.points (j + 2))
  have hA : A ∈ T.edge i := by rw [← he]; exact left_mem_segment ℝ A B
  have hB : B ∈ T.edge i := by rw [← he]; exact right_mem_segment ℝ A B
  have hP : T.points (i + 1) ∈ segment ℝ A B := by
    change T.points (i + 1) ∈ T.cornerSection S i j
    rw [he, edge_eq_segment]
    exact left_mem_segment ℝ _ _
  have hQ : T.points (i + 2) ∈ segment ℝ A B := by
    change T.points (i + 2) ∈ T.cornerSection S i j
    rw [he, edge_eq_segment]
    exact right_mem_segment ℝ _ _
  have hP' := (mem_extremePoints_iff_forall_segment.mp (T.vertex_mem_extremePoints (i + 1))).2
    A hA.1 B hB.1 hP
  have hQ' := (mem_extremePoints_iff_forall_segment.mp (T.vertex_mem_extremePoints (i + 2))).2
    A hA.1 B hB.1 hQ
  have hne : T.points (i + 1) ≠ T.points (i + 2) := T.independent.injective.ne
    ((by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i)
  rcases hP' with hp | hp <;> rcases hQ' with hq | hq
  · exact False.elim (hne (hp.symm.trans hq))
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hq, hp⟩
  · exact False.elim (hne (hp.symm.trans hq))

theorem segment_subset_edge_of_cornerProject (T : Triangle) (i k l : Fin 3)
    {p : Plane} (hp : p ∈ T.support) (hne : p ≠ T.points i)
    (hli : l ≠ i) (hlk : l ≠ k) (he : T.cornerProject i p = T.points k) :
    segment ℝ (T.points i) p ⊆ T.edge l := by
  apply (T.edge_convex l).segment_subset
  · refine ⟨T.vertex_mem_support i, ?_⟩
    change T.coord l (T.points i) = 0
    rw [coord_vertex, if_neg hli]
  · refine ⟨hp, ?_⟩
    have hc := T.cornerProject_coord_other i l hli p
    rw [he, coord_vertex, if_neg hlk] at hc
    exact (div_eq_zero_iff.mp hc.symm).resolve_right (T.cornerScale_pos i hp hne).ne'

theorem adjacent_edges_of_section_eq (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) (hO : S.points j = T.points i)
    (he : T.cornerSection S i j = T.edge i) :
    (S.edge (j + 2) ⊆ T.edge (i + 2) ∧ S.edge (j + 1) ⊆ T.edge (i + 1)) ∨
    (S.edge (j + 2) ⊆ T.edge (i + 1) ∧ S.edge (j + 1) ⊆ T.edge (i + 2)) := by
  have hj11 : j + 1 + 1 = j + 2 := by fin_cases j <;> rfl
  have hj12 : j + 1 + 2 = j := by fin_cases j <;> rfl
  have hj21 : j + 2 + 1 = j := by fin_cases j <;> rfl
  have hj22 : j + 2 + 2 = j + 1 := by fin_cases j <;> rfl
  have hA := hST (S.vertex_mem_support (j + 1))
  have hB := hST (S.vertex_mem_support (j + 2))
  have hAn := T.corner_other_ne S i j (j + 1) hO ((by decide : ∀ j : Fin 3, j + 1 ≠ j) j)
  have hBn := T.corner_other_ne S i j (j + 2) hO ((by decide : ∀ j : Fin 3, j + 2 ≠ j) j)
  have h1 : i + 1 ≠ i := (by decide : ∀ i : Fin 3, i + 1 ≠ i) i
  have h2 : i + 2 ≠ i := (by decide : ∀ i : Fin 3, i + 2 ≠ i) i
  have h12 : i + 1 ≠ i + 2 := (by decide : ∀ i : Fin 3, i + 1 ≠ i + 2) i
  rw [S.edge_eq_segment (j + 2), S.edge_eq_segment (j + 1)]
  simp only [hj11, hj12, hj21, hj22, hO]
  rw [segment_symm ℝ (S.points (j + 2)) (T.points i)]
  rcases T.cornerProject_pair_of_section_eq S i j he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    exact ⟨T.segment_subset_edge_of_cornerProject i (i + 1) (i + 2) hA hAn h2 h12.symm ha,
      T.segment_subset_edge_of_cornerProject i (i + 2) (i + 1) hB hBn h1 h12 hb⟩
  · right
    exact ⟨T.segment_subset_edge_of_cornerProject i (i + 2) (i + 1) hA hAn h1 h12 ha,
      T.segment_subset_edge_of_cornerProject i (i + 1) (i + 2) hB hBn h2 h12.symm hb⟩

end Triangle

namespace Tiling

theorem boundarySideCount_pos_of_edge {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (k : Fin n)
    (he : (d.tile.move (d.place k)).edge j ⊆ T.edge i) : 0 < d.boundarySideCount i j := by
  classical
  apply Finset.card_pos.mpr
  exact ⟨⟨(k, j), he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem adjacent_counts_pos_of_min {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i : Fin 3) (hmin : ∀ j, T.angle i ≤ d.tile.angle j) (e : d.CornerPiece i) :
    (0 < d.boundarySideCount (i + 2) (e.val.2 + 2) ∧
      0 < d.boundarySideCount (i + 1) (e.val.2 + 1)) ∨
    (0 < d.boundarySideCount (i + 1) (e.val.2 + 2) ∧
      0 < d.boundarySideCount (i + 2) (e.val.2 + 1)) := by
  have hST : (d.tile.move (d.place e.val.1)).support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  rcases T.adjacent_edges_of_section_eq (d.tile.move (d.place e.val.1)) hST i e.val.2
    e.property (d.cornerSection_eq_edge_of_min i hmin e) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨d.boundarySideCount_pos_of_edge _ _ _ ha,
      d.boundarySideCount_pos_of_edge _ _ _ hb⟩
  · exact Or.inr ⟨d.boundarySideCount_pos_of_edge _ _ _ ha,
      d.boundarySideCount_pos_of_edge _ _ _ hb⟩

end Tiling

end Erdos633b

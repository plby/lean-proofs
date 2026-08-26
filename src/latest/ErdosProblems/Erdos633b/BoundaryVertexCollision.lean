import ErdosProblems.Erdos633b.BoundarySegmentChain
import ErdosProblems.Erdos633b.ReptilingTrace

/-! If a boundary side contains no edge opposite a tile angle larger than
both outer endpoint angles, two distinct tiles place that angle at one interior boundary point. -/

namespace Erdos633b

namespace Triangle

theorem edge_index_unique_of_subsets (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j k : Fin 3) (hj : S.edge j ⊆ T.edge i) (hk : S.edge k ⊆ T.edge i) : j = k := by
  by_contra hne
  obtain ⟨l, hl⟩ := T.exists_vertex_coord_pos_of_subset S hST i
  have hm : S.points l ∈ T.edge i := by
    by_cases hlj : l = j
    · exact hk (S.edge_vertex_mem k l (by simpa only [hlj] using hne))
    · exact hj (S.edge_vertex_mem j l hlj)
  exact hl.ne' hm.2

end Triangle

namespace Tiling

theorem boundaryEdge_tile_injective {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin 3) :
    Function.Injective (fun e : d.BoundaryEdge i => e.val.1) := by
  intro e f he
  change e.val.1 = f.val.1 at he
  have hST : (d.tile.move (d.place e.val.1)).support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset e.val.1
  have hf : (d.tile.move (d.place e.val.1)).edge f.val.2 ⊆ T.edge i := by
    rw [he]
    exact f.property
  have hi := T.edge_index_unique_of_subsets (d.tile.move (d.place e.val.1)) hST
    i e.val.2 f.val.2 e.property hf
  exact Subtype.ext (Prod.ext he hi)

theorem tile_angle_le_of_vertex {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (k : Fin n) (h : d.place k (d.tile.points j) = T.points i) :
    d.tile.angle j ≤ T.angle i := by
  let e : d.CornerPiece i := ⟨(k, j), h⟩
  rw [d.angle_eq_sum_cornerPieces]
  exact Finset.single_le_sum (fun f _ => (d.tile.angle_pos f.val.2).le) (Finset.mem_univ e)

theorem boundary_two_angle_vertices {T : Triangle} {n : ℕ} (d : Tiling T n)
    (i j : Fin 3) (hcount : d.boundarySideCount i j = 0)
    (hP : T.angle (i + 1) < d.tile.angle j) (hQ : T.angle (i + 2) < d.tile.angle j) :
    ∃ a b : Fin n, a ≠ b ∧ ∃ p : Plane, p ∈ T.openEdge i ∧
      d.place a (d.tile.points j) = p ∧ d.place b (d.tile.points j) = p := by
  let selected : d.BoundaryEdge i → Plane := fun e => d.place e.val.1 (d.tile.points j)
  have hidx (e : d.BoundaryEdge i) : j ≠ e.val.2 := by
    intro hj
    have hc := d.boundarySideCount_pos_of_edge i e.val.2 e.val.1 e.property
    rw [← hj, hcount] at hc
    exact Nat.lt_irrefl 0 hc
  have hend (e : d.BoundaryEdge i) :
      selected e = (d.tile.move (d.place e.val.1)).points (e.val.2 + 1) ∨
      selected e = (d.tile.move (d.place e.val.1)).points (e.val.2 + 2) := by
    rcases (by decide : ∀ j k : Fin 3, j ≠ k → j = k + 1 ∨ j = k + 2)
      j e.val.2 (hidx e) with hj | hj
    · exact Or.inl (by change d.place e.val.1 (d.tile.points j) = _; rw [hj]; rfl)
    · exact Or.inr (by change d.place e.val.1 (d.tile.points j) = _; rw [hj]; rfl)
  have hneP (e : d.BoundaryEdge i) : selected e ≠ T.points (i + 1) := by
    intro he
    exact (not_le_of_gt hP) (d.tile_angle_le_of_vertex (i + 1) j e.val.1 he)
  have hneQ (e : d.BoundaryEdge i) : selected e ≠ T.points (i + 2) := by
    intro he
    exact (not_le_of_gt hQ) (d.tile_angle_le_of_vertex (i + 2) j e.val.1 he)
  obtain ⟨e, f, hef, hp⟩ := d.boundary_endpoint_collision i selected hend hneP hneQ
  have hmem : selected e ∈ T.edge i :=
    e.property ((d.tile.move (d.place e.val.1)).edge_vertex_mem e.val.2 j (hidx e))
  have hopen : selected e ∈ T.openEdge i := by
    rw [T.openEdge_eq_openSegment]
    apply mem_openSegment_of_ne_left_right (hneP e).symm (hneQ e).symm
    rwa [← T.edge_eq_segment]
  exact ⟨e.val.1, f.val.1, (d.boundaryEdge_tile_injective i).ne hef,
    selected e, hopen, rfl, hp.symm⟩

theorem boundaryMatrix_last_diagonal_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (hmin : ∀ j, j ≠ 0 → d.tile.angle 0 < d.tile.angle j) : d.boundaryMatrix 2 2 = 0 := by
  rcases d.boundaryMatrix_corner_alternative hn h hmin with hd | ⟨_, _, _, _, _, _, h22⟩
  · exact hd 2
  · exact h22

theorem reptiling_two_largest_vertices {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hn : ¬ IsSquare n) (h : ∀ i, d.tile.angle i = T.angle i)
    (h01 : d.tile.angle 0 < d.tile.angle 1) (h12 : d.tile.angle 1 < d.tile.angle 2) :
    ∃ a b : Fin n, a ≠ b ∧ ∃ p : Plane, p ∈ T.openEdge 2 ∧
      d.place a (d.tile.points 2) = p ∧ d.place b (d.tile.points 2) = p := by
  have hmin (j : Fin 3) (hj : j ≠ 0) : d.tile.angle 0 < d.tile.angle j := by
    fin_cases j
    · exact False.elim (hj rfl)
    · exact h01
    · exact h01.trans h12
  have hz := d.boundaryMatrix_last_diagonal_zero hn h hmin
  have hc : d.boundarySideCount 2 2 = 0 := by
    unfold boundaryMatrix at hz
    exact_mod_cast hz
  apply d.boundary_two_angle_vertices 2 2 hc
  · change T.angle 0 < d.tile.angle 2
    rw [← h 0]
    exact h01.trans h12
  · change T.angle 1 < d.tile.angle 2
    rw [← h 1]
    exact h12

end Tiling

end Erdos633b

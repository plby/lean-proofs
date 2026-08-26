import ErdosProblems.Erdos633b.OpenEdgeIncidence
import ErdosProblems.Erdos633b.BoundaryEdgeOrientation

/-! Away from placed vertices an outer open side has one incident tile
edge, with the same positive direction as the outer side. -/

namespace Erdos633b
namespace Triangle

theorem edge_subset_of_openEdge_mem_edge (T S : Triangle) (hST : S.support ⊆ T.support)
    (i j : Fin 3) {p : Plane} (hpS : p ∈ S.openEdge j) (hpT : p ∈ T.edge i) :
    S.edge j ⊆ T.edge i := by
  have hp : p ∈ S.support ∩ T.edge i := ⟨(S.openEdge_subset_edge j hpS).1, hpT⟩
  rcases T.support_inter_edge_cases S hST i with h | ⟨k, h⟩ | ⟨k, h⟩
  · rw [h] at hp
    exact hp.elim
  · rw [h, Set.mem_singleton_iff] at hp
    rw [hp] at hpS
    exact (S.vertex_not_mem_openEdge j k hpS).elim
  · have hpk : p ∈ S.edge k := h ▸ hp
    have hkj : k = j := by
      by_contra hn
      have hpos := hpS.2 k hn
      rw [hpk.2] at hpos
      exact lt_irrefl _ hpos
    rw [← hkj, ← h]
    exact Set.inter_subset_right

end Triangle
namespace Tiling

theorem boundary_edgePiece_subset {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (i : Fin 3) (hp : p ∈ T.edge i) (e : d.EdgePiece p) :
    (d.tile.move (d.place e.val.1)).edge e.val.2 ⊆ T.edge i := by
  apply T.edge_subset_of_openEdge_mem_edge _ _ i e.val.2 e.property hp
  rw [Triangle.support_move]
  exact d.piece_subset e.val.1

theorem boundary_edgePiece_subsingleton {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (i : Fin 3) (hp : p ∈ T.edge i) : Subsingleton (d.EdgePiece p) := by
  refine ⟨fun e f => ?_⟩
  by_contra hef
  have htile := fun h => hef (d.edgePiece_tile_injective p h)
  exact Set.disjoint_left.mp (d.boundary_openEdges_disjoint htile i e.val.2 f.val.2
    (d.boundary_edgePiece_subset i hp e) (d.boundary_edgePiece_subset i hp f))
      e.property f.property

theorem boundary_edgePiece_nonempty {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (i : Fin 3) (hp : p ∈ T.edge i) (hv : p ∉ d.vertices) :
    Nonempty (d.EdgePiece p) := by
  have hpT := hp.1
  rw [← d.covers, Set.mem_iUnion] at hpT
  obtain ⟨b, hb⟩ := hpT
  have hST : (d.tile.move (d.place b)).support ⊆ T.support := by
    rw [Triangle.support_move]
    exact d.piece_subset b
  have hpB : p ∈ (d.tile.move (d.place b)).support := by
    rwa [Triangle.support_move]
  have hn : p ∉ interior (d.tile.move (d.place b)).support := by
    intro h
    have hc := (T.mem_interior_support_iff_all_coords p).mp (interior_mono hST h) i
    rw [hp.2] at hc
    exact lt_irrefl _ hc
  obtain ⟨j, hj⟩ := (d.tile.move (d.place b)).openEdge_of_not_interior_nonvertex hpB hn
    (fun j he => hv ⟨(b, j), he.symm⟩)
  exact ⟨⟨(b, j), hj⟩⟩

theorem boundary_edgePiece_card_eq_one {T : Triangle} {n : ℕ} (d : Tiling T n)
    {p : Plane} (i : Fin 3) (hp : p ∈ T.edge i) (hv : p ∉ d.vertices) :
    Fintype.card (d.EdgePiece p) = 1 := by
  let _ := d.boundary_edgePiece_subsingleton i hp
  let _ := d.boundary_edgePiece_nonempty i hp hv
  have hlo := Fintype.card_pos (α := d.EdgePiece p)
  have hhi := Fintype.card_le_one_iff_subsingleton.mpr
    (d.boundary_edgePiece_subsingleton i hp)
  omega

theorem boundary_edgePiece_direction {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) (u : Plane) {p : Plane}
    (i : Fin 3) (hp : p ∈ T.edge i) (e : d.EdgePiece p) :
    (d.tile.move (d.place e.val.1)).positiveEdgeDirection o u e.val.2 =
      T.positiveEdgeDirection o u i := by
  apply T.boundary_positiveEdgeDirections _ o u _ i e.val.2
    (d.boundary_edgePiece_subset i hp e)
  rw [Triangle.support_move]
  exact d.piece_subset e.val.1

end Tiling
end Erdos633b

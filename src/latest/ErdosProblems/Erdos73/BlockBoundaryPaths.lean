import ErdosProblems.Erdos73.BrickBlockPacking

/-! The block paths attach on the actual wall boundary, not on the added segments. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def internalVertexBoundary (K : SimpleGraph V) (T : Finset V) : Finset V :=
  T.filter (fun x => ∃ y, y ∉ T ∧ K.Adj x y)

theorem IsParityBreakingPath.source_mem_boundary {T : Finset V}
    (c : BipartiteColoringOn G T) {P : Erdos73Infrastructure.SimpleGraph.GraphPath G}
    (hP : IsParityBreakingPath c.color T P) (K L : SimpleGraph V)
    (hPKL : GraphPath.actualEdgeGraph P ≤ K ⊔ L)
    (hL : ∀ x y, L.Adj x y → x ∉ T) : P.source ∈ internalVertexBoundary K T := by
  have hnil : ¬ P.walk.Nil := fun hn => hP.breaking.source_ne_target hn.eq
  have hpedge : (GraphPath.actualEdgeGraph P).Adj P.source P.walk.snd :=
    P.walk.toSubgraph_adj_snd hnil
  have hsnd : P.walk.snd ∉ T := fun hh => hP.no_edge_in_terminals c hpedge hP.source_mem hh
  have hK : K.Adj P.source P.walk.snd := by
    rcases hPKL hpedge with hh | hh
    · exact hh
    · exact (hL _ _ hh hP.source_mem).elim
  exact mem_filter.mpr ⟨hP.source_mem, P.walk.snd, hsnd, hK⟩

theorem IsParityBreakingPath.endpoints_mem_boundary {T : Finset V}
    (c : BipartiteColoringOn G T) {P : Erdos73Infrastructure.SimpleGraph.GraphPath G}
    (hP : IsParityBreakingPath c.color T P) (K L : SimpleGraph V)
    (hPKL : GraphPath.actualEdgeGraph P ≤ K ⊔ L)
    (hL : ∀ x y, L.Adj x y → x ∉ T) :
    P.source ∈ internalVertexBoundary K T ∧ P.target ∈ internalVertexBoundary K T := by
  refine ⟨hP.source_mem_boundary c K L hPKL hL, ?_⟩
  apply hP.reverse.source_mem_boundary c K L
  · simpa only [GraphPath.actualEdgeGraph_reverse] using hPKL
  · exact hL

theorem BrickStripSelectionState.block_path_endpoints_on_wall_boundary
    [Fintype V] {c r m h : ℕ} {S : GraphSubdivisionModel (elementaryWall c r) G}
    {P : Fin m → Erdos73Infrastructure.SimpleGraph.GraphPath G}
    (col : BipartiteColoringOn G S.vertexSet) (st : BrickStripSelectionState S col.color P h)
    (a d : ℕ) (ha : a + d ≤ c - 1)
    (hUT : ∀ j, Disjoint (st.segment j).path.vertexSet (brickColumnBlock S a d ha))
    (B : Erdos73Infrastructure.SimpleGraph.GraphPath G)
    (hB : IsParityBreakingPath col.color (brickColumnBlock S a d ha) B)
    (hBJ : GraphPath.actualEdgeGraph B ≤ st.wallSegmentGraph col) :
    B.source ∈ internalVertexBoundary S.actualEdgeGraph (brickColumnBlock S a d ha) ∧
      B.target ∈ internalVertexBoundary S.actualEdgeGraph (brickColumnBlock S a d ha) := by
  apply hB.endpoints_mem_boundary (col.mono_support (brickColumnBlock_subset S a d ha))
    S.actualEdgeGraph (⨆ j, GraphPath.actualEdgeGraph (st.segment j).path) hBJ
  intro x y hxy hxT
  obtain ⟨j, hxy⟩ := SimpleGraph.iSup_adj.mp hxy
  exact Finset.disjoint_left.mp (hUT j)
    (GraphPath.actualEdgeGraph_adj_support (st.segment j).path hxy).1 hxT

end
end Erdos73

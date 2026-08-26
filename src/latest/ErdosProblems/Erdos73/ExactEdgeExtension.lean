import ErdosProblems.Erdos73.CleanPathEdges
import ErdosProblems.Erdos73.ParityGraphTransport
import ErdosProblems.Erdos73.ParityNetworkExtension
import ErdosProblems.Erdos73.RobustConnectedSupport

/-! Route through a retained-edge network and then remove all terminal-region edges. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {D T : Finset V}

theorem exists_exact_edge_network_extension
    (c : BipartiteColoringOn G (D ∪ T)) (U : Erdos73Infrastructure.SimpleGraph.GraphPath G)
    (hU : IsParityBreakingPath c.color D U) (hUT : Disjoint U.vertexSet T)
    (J K L : SimpleGraph V) (hJG : J ≤ G)
    (hUJ : GraphPath.actualEdgeGraph U ≤ J) (hJKL : J ≤ K ⊔ L)
    (hK : ∀ x y, K.Adj x y → x ∈ D ∪ U.vertexSet ∧ y ∈ D ∪ U.vertexSet)
    (hL : ∀ x y, L.Adj x y → x ∈ T ∧ y ∈ T)
    (hconn : DeletionOneConnected J (D ∪ T)) (hT : 2 ≤ T.card) :
    ∃ B : Erdos73Infrastructure.SimpleGraph.GraphPath G,
      IsParityBreakingPath c.color T B ∧ B.vertexSet ⊆ D ∪ U.vertexSet ∧
        GraphPath.actualEdgeGraph B ≤ J := by
  have hUR : IsParityBreakingPath c.color (D ∪ T) U := by
    refine ⟨mem_union_left _ hU.source_mem, mem_union_left _ hU.target_mem, hU.breaking, ?_⟩
    intro x hx hxR
    rcases mem_union.mp hxR with hxD | hxT
    · exact hU.internal_disjoint x hx hxD
    · exact (Finset.disjoint_left.mp hUT hx hxT).elim
  let hUedges := GraphPath.edges_mem_of_actualEdgeGraph_le U hUJ
  let Q := U.transfer J hUedges
  let cJ := c.mono_graph hJG
  have hQ : IsParityBreakingPath cJ.color (D ∪ T) Q := hUR.transfer J hUedges
  obtain ⟨B, hB, _⟩ := exists_parityBreaking_network_extension cJ Q hQ
    (show D ∪ T ⊆ D ∪ T from subset_rfl) hQ.source_mem hQ.target_mem
    subset_union_right hT hconn.induced_delete_preconnected
  have hBK : GraphPath.actualEdgeGraph B ≤ K :=
    hB.actualEdgeGraph_le_of_sup (cJ.mono_support (show T ⊆ D ∪ T from subset_union_right))
      K L hJKL hL
  have hpos : 0 < B.walk.length := Walk.not_nil_iff_lt_length.mp
    (fun hn => hB.breaking.source_ne_target hn.eq)
  have hBD : B.vertexSet ⊆ D ∪ U.vertexSet :=
    path_vertexSet_subset_of_edge_support B hpos _ (fun x y hxy => hK x y (hBK hxy))
  refine ⟨B.mapLe hJG, hB.mapLe hJG, ?_, ?_⟩
  · simpa only [Erdos73Infrastructure.SimpleGraph.GraphPath.mapLe_vertexSet] using hBD
  · rw [GraphPath.actualEdgeGraph_mapLe]
    exact GraphPath.actualEdgeGraph_le B

end
end Erdos73

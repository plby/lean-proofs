import ErdosProblems.Erdos73.SubdivisionEdgeGraph
import ErdosProblems.Erdos73.ParityColoring

/-! A breaking terminal-clean path uses no edge internal to the balanced terminal support. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem path_length_one_of_endpoint_edge (P : Erdos73Infrastructure.SimpleGraph.GraphPath G)
    (hadj : P.walk.toSubgraph.Adj P.source P.target) : P.walk.length = 1 := by
  obtain ⟨i, _, hi⟩ := P.walk.toSubgraph_adj_iff.mp hadj
  have he : P.walk.getVert 1 = P.walk.getVert P.walk.length := by
    simpa only [Walk.getVert_length] using P.isPath.snd_of_toSubgraph_adj hadj
  exact (P.isPath.getVert_injOn (show 1 ≤ P.walk.length by omega)
    (show P.walk.length ≤ P.walk.length from le_rfl) he).symm

theorem path_support_subset_endpoints_of_length_one
    (P : Erdos73Infrastructure.SimpleGraph.GraphPath G) (hP : P.walk.length = 1) :
    ∀ x ∈ P.vertexSet, x = P.source ∨ x = P.target := by
  intro x hx
  obtain ⟨n, hn, hle⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hx)
  have hcases : n = 0 ∨ n = P.walk.length := by omega
  rcases hcases with h0 | hl
  · left
    simpa only [h0, Walk.getVert_zero] using hn.symm
  · right
    simpa only [hl, Walk.getVert_length] using hn.symm

theorem IsParityBreakingPath.no_edge_in_terminals {T : Finset V}
    (c : BipartiteColoringOn G T) {P : Erdos73Infrastructure.SimpleGraph.GraphPath G}
    (hP : IsParityBreakingPath c.color T P) {x y : V}
    (hxy : (GraphPath.actualEdgeGraph P).Adj x y) (hx : x ∈ T) (hy : y ∈ T) : False := by
  have hpverts := GraphPath.actualEdgeGraph_adj_support P hxy
  have hxend := hP.internal_disjoint x hpverts.1 hx
  have hyend := hP.internal_disjoint y hpverts.2 hy
  have hend : P.walk.toSubgraph.Adj P.source P.target := by
    rcases hxend with rfl | rfl <;> rcases hyend with rfl | rfl
    · exact (G.loopless.irrefl _ (GraphPath.actualEdgeGraph_le P hxy)).elim
    · exact hxy
    · exact hxy.symm
    · exact (G.loopless.irrefl _ (GraphPath.actualEdgeGraph_le P hxy)).elim
  have hlen := path_length_one_of_endpoint_edge P hend
  apply c.not_parityBreaking_of_subset P _ hP.breaking
  intro v hv
  exact (path_support_subset_endpoints_of_length_one P hlen v hv).elim
    (fun he => he ▸ hP.source_mem) (fun he => he ▸ hP.target_mem)

theorem IsParityBreakingPath.actualEdgeGraph_le_of_sup {T : Finset V}
    (c : BipartiteColoringOn G T) {P : Erdos73Infrastructure.SimpleGraph.GraphPath G}
    (hP : IsParityBreakingPath c.color T P) (K L : SimpleGraph V) (hG : G ≤ K ⊔ L)
    (hL : ∀ x y, L.Adj x y → x ∈ T ∧ y ∈ T) : GraphPath.actualEdgeGraph P ≤ K := by
  intro x y hxy
  rcases hG (GraphPath.actualEdgeGraph_le P hxy) with hK | hLy
  · exact hK
  · exact (hP.no_edge_in_terminals c hxy (hL x y hLy).1 (hL x y hLy).2).elim

theorem path_vertexSet_subset_of_edge_support
    (P : Erdos73Infrastructure.SimpleGraph.GraphPath G) (hpos : 0 < P.walk.length)
    (D : Finset V) (hD : ∀ x y, (GraphPath.actualEdgeGraph P).Adj x y → x ∈ D ∧ y ∈ D) :
    P.vertexSet ⊆ D := by
  intro x hx
  obtain ⟨n, hn, hle⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hx)
  by_cases hlt : n < P.walk.length
  · have hh := (hD _ _ (P.walk.toSubgraph_adj_getVert hlt)).1
    exact hn ▸ hh
  · have he : n = P.walk.length := by omega
    have hh := (hD _ _ (P.walk.toSubgraph_adj_getVert (by
      omega : P.walk.length - 1 < P.walk.length))).2
    have he' : P.walk.getVert (P.walk.length - 1 + 1) = x := by
      rw [Nat.sub_add_cancel hpos, ← he]
      exact hn
    exact he' ▸ hh

end
end Erdos73

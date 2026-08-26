/- Boundary-proper linkage deletion (qualitative Leaf--Seymour 3.3). -/
import ErdosProblems.Erdos73.BoundaryPaths
import ErdosProblems.Erdos73.LinkageDeletion

namespace Erdos73Infrastructure.SimpleGraph
namespace PathPacking
variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {A B S T Z D : Finset V}

/-- Terminal cleaning in the union of two proper linkages preserves
properness, provided the output avoids the deleted set. -/
theorem boundaryProper_of_clean_avoiding
    (P : PathPacking G A B) (Q : PathPacking G S T)
    (hP : P.IsBoundaryProper Z) (hQ : Q.IsBoundaryProper Z)
    (hAZ : A ⊆ Z) (hBZ : B ⊆ Z)
    (R : GraphPath (P.spanningGraph ⊔ Q.spanningGraph))
    (hR : R.Connects (A \ D) (B \ D))
    (hclean : R.InternallyDisjointFromSet ((A \ D) ∪ (B \ D)))
    (havoid : Disjoint R.vertexSet D) : R.IsBoundaryProper Z := by
  have hs : R.source ∈ Z := by
    rcases hR with h | h
    · exact hAZ (Finset.mem_sdiff.mp h.1).1
    · exact hBZ (Finset.mem_sdiff.mp h.1).1
  have ht : R.target ∈ Z := by
    rcases hR with h | h
    · exact hBZ (Finset.mem_sdiff.mp h.2).1
    · exact hAZ (Finset.mem_sdiff.mp h.2).1
  refine ⟨hs, ht, ?_, ?_⟩
  · intro x hx hxZ
    by_cases hxAB : x ∈ A ∪ B
    · apply hclean hx
      have hxD : x ∉ D := fun h => Finset.disjoint_left.mp havoid hx h
      rcases Finset.mem_union.mp hxAB with hxA | hxB
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxA, hxD⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxB, hxD⟩)
    · have hxP := hP.not_mem_vertexSet_of_not_mem_terminals hxZ hxAB
      apply R.isEndpoint_of_mem_vertexSet_of_neighbors_eq ?_ hx
      intro y z hxy hxz
      have hyQ : Q.spanningGraph.Adj x y :=
        hxy.resolve_left (P.not_adj_spanningGraph_of_not_mem_vertexSet hxP)
      have hzQ : Q.spanningGraph.Adj x z :=
        hxz.resolve_left (P.not_adj_spanningGraph_of_not_mem_vertexSet hxP)
      exact hQ.boundary_neighbors_eq hxZ hyQ hzQ
  · intro hlen
    have ha := _root_.SimpleGraph.Walk.adj_of_length_eq_one hlen
    rcases ha with ha | ha
    · exact hP.no_boundary_edge hs ht ha
    · exact hQ.no_boundary_edge hs ht ha

end PathPacking
end Erdos73Infrastructure.SimpleGraph

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph

/-- Delete one member of a sufficiently large proper linkage while
retaining a proper sublinkage of a fixed positive fraction of the rows. -/
theorem boundaryProper_linkage_avoiding_path
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {A B S T Z : Finset V}
    (P : PathPacking G A B) (Q : PathPacking G S T)
    (hP : P.IsBoundaryProper Z) (hQ : Q.IsBoundaryProper Z)
    (hAZ : A ⊆ Z) (hBZ : B ⊆ Z)
    (g h : ℕ) (hh : 0 < h) (hm : qualitativeGrillRows g h ≤ P.card)
    (hsize : (P.card + 1) * (2 * qualitativeGrillColumns g h) ≤ Q.card)
    (hgrid : ¬ IsMinor (squareGrid g) G)
    (hbip : ¬ IsMinor (completeBipartiteGraph (Fin h) (Fin h)) G) :
    ∃ i : Q.Index, ∃ R : PathPacking G (A \ (Q.path i).vertexSet) (B \ (Q.path i).vertexSet),
      P.card / (2 * qualitativeGrillRows g h) + 1 ≤ R.card ∧
      (∀ r, Disjoint (R.path r).vertexSet (Q.path i).vertexSet) ∧ R.IsBoundaryProper Z := by
  let J := P.spanningGraph ⊔ Q.spanningGraph
  have hJG : J ≤ G := sup_le P.spanningGraph_le Q.spanningGraph_le
  let PJ : PathPacking J A B := P.inSpanningGraph.mapLe le_sup_left
  let QJ : PathPacking J S T := Q.inSpanningGraph.mapLe le_sup_right
  have hQverts (i : Q.Index) : (QJ.path i).vertexSet = (Q.path i).vertexSet := by
    change (((Q.inSpanningGraph.path i).mapLe le_sup_right).vertexSet) = _
    rw [GraphPath.mapLe_vertexSet]
    simp only [PathPacking.inSpanningGraph, PathPacking.transfer, GraphPath.transfer_vertexSet]
  have hconn (i : Q.Index) : (J.induce ((Q.path i).vertexSet : Set V)).Connected := by
    have hc := (QJ.path i).connected_induce_vertexSet
    rw [hQverts i] at hc
    exact hc
  obtain ⟨i, R, hcard, havoid⟩ := linkage_avoiding_connected_column PJ
    (fun i : Q.Index => (Q.path i).vertexSet)
    (fun i => ⟨_, (Q.path i).source_mem_vertexSet⟩) hconn Q.node_disjoint
    g h hh hm hsize (fun h => hgrid (h.mono hJG)) (fun h => hbip (h.mono hJG))
  let C := R.cleanToTerminals
  have hCavoid (r : C.Index) : Disjoint (C.path r).vertexSet (Q.path i).vertexSet :=
    (havoid r).mono_left (R.cleanToTerminals_path_vertexSet_subset r)
  have hCproper : C.IsBoundaryProper Z := by
    intro r
    exact P.boundaryProper_of_clean_avoiding Q hP hQ hAZ hBZ (C.path r)
      (C.connects r) (R.cleanToTerminals_terminalClean r) (hCavoid r)
  refine ⟨i, C.mapLe hJG, hcard, ?_, ?_⟩
  · intro r
    change Disjoint ((C.path r).mapLe hJG).vertexSet (Q.path i).vertexSet
    rw [GraphPath.mapLe_vertexSet]
    exact hCavoid r
  · intro r
    exact (hCproper r).mapLe hJG

end
end Erdos73

import ErdosProblems.Erdos73.SubdivisionSupports

/-! Retain exactly the corridor edges and transfer actual subdivision models to subgraphs. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

namespace GraphPath

variable {V : Type*} {G : SimpleGraph V}

def actualEdgeGraph (P : Erdos73Infrastructure.SimpleGraph.GraphPath G) : SimpleGraph V :=
  P.walk.toSubgraph.spanningCoe

theorem actualEdgeGraph_le (P : Erdos73Infrastructure.SimpleGraph.GraphPath G) :
    actualEdgeGraph P ≤ G := P.walk.toSubgraph.spanningCoe_le

theorem actualEdgeGraph_reverse (P : Erdos73Infrastructure.SimpleGraph.GraphPath G) :
    actualEdgeGraph P.reverse = actualEdgeGraph P := by
  simp only [actualEdgeGraph, Erdos73Infrastructure.SimpleGraph.GraphPath.reverse,
    Walk.toSubgraph_reverse]

theorem actualEdgeGraph_mapLe (P : Erdos73Infrastructure.SimpleGraph.GraphPath G)
    {J : SimpleGraph V} (hGJ : G ≤ J) : actualEdgeGraph (P.mapLe hGJ) = actualEdgeGraph P := by
  ext x y
  change (P.walk.mapLe hGJ).toSubgraph.Adj x y ↔ P.walk.toSubgraph.Adj x y
  simp only [Walk.adj_toSubgraph_iff_mem_edges, Walk.edges_mapLe_eq_edges]

theorem actualEdgeGraph_adj_support (P : Erdos73Infrastructure.SimpleGraph.GraphPath G)
    {x y : V} (hxy : (actualEdgeGraph P).Adj x y) : x ∈ P.vertexSet ∧ y ∈ P.vertexSet := by
  exact ⟨List.mem_toFinset.mpr (P.walk.mem_verts_toSubgraph.mp
    (P.walk.toSubgraph.edge_vert hxy)), List.mem_toFinset.mpr
      (P.walk.mem_verts_toSubgraph.mp (P.walk.toSubgraph.edge_vert hxy.symm))⟩

theorem edges_mem_of_actualEdgeGraph_le (P : Erdos73Infrastructure.SimpleGraph.GraphPath G)
    {J : SimpleGraph V} (hJ : actualEdgeGraph P ≤ J) :
    ∀ e, e ∈ P.walk.edges → e ∈ J.edgeSet := by
  intro e he
  apply SimpleGraph.edgeSet_mono hJ
  change e ∈ P.walk.toSubgraph.spanningCoe.edgeSet
  rw [Subgraph.edgeSet_spanningCoe]
  exact P.walk.mem_edges_toSubgraph.mpr he

end GraphPath

namespace GraphSubdivisionModel

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

def actualEdgeGraph (S : GraphSubdivisionModel H G) : SimpleGraph V :=
  ⨆ e, GraphPath.actualEdgeGraph (S.edgePath e)

theorem actualEdgeGraph_le (S : GraphSubdivisionModel H G) : S.actualEdgeGraph ≤ G :=
  iSup_le fun e => GraphPath.actualEdgeGraph_le (S.edgePath e)

theorem actualEdgeGraph_adj_support (S : GraphSubdivisionModel H G) {x y : V}
    (hxy : S.actualEdgeGraph.Adj x y) : x ∈ S.vertexSet ∧ y ∈ S.vertexSet := by
  obtain ⟨e, he⟩ := SimpleGraph.iSup_adj.mp hxy
  obtain ⟨hx, hy⟩ := GraphPath.actualEdgeGraph_adj_support (S.edgePath e) he
  exact ⟨(S.mem_vertexSet x).mpr (Or.inr ⟨e, hx⟩),
    (S.mem_vertexSet y).mpr (Or.inr ⟨e, hy⟩)⟩

def transferTo (S : GraphSubdivisionModel H G) (J : SimpleGraph V)
    (hJ : S.actualEdgeGraph ≤ J) : GraphSubdivisionModel H J where
  branchVertex := S.branchVertex
  injective := S.injective
  edgePath := fun e => (S.edgePath e).transfer J
    (GraphPath.edges_mem_of_actualEdgeGraph_le _ ((le_iSup _ e).trans hJ))
  source_eq := S.source_eq
  target_eq := S.target_eq
  branch_on_path := by
    intro e w hw
    rw [Erdos73Infrastructure.SimpleGraph.GraphPath.transfer_vertexSet] at hw
    exact S.branch_on_path e w hw
  intersection := by
    intro e f hef x hx hy
    rw [Erdos73Infrastructure.SimpleGraph.GraphPath.transfer_vertexSet] at hx hy
    exact S.intersection hef x hx hy

theorem transferTo_vertexSet (S : GraphSubdivisionModel H G) (J : SimpleGraph V)
    (hJ : S.actualEdgeGraph ≤ J) : (S.transferTo J hJ).vertexSet = S.vertexSet := by
  ext x
  simp only [mem_vertexSet, transferTo,
    Erdos73Infrastructure.SimpleGraph.GraphPath.transfer_vertexSet]

theorem restrictCopy_actualEdgeGraph_le {U : Type*} [Fintype U] [LinearOrder U]
    {F : SimpleGraph U} (S : GraphSubdivisionModel H G) (f : F.Copy H) :
    (S.restrictCopy f).actualEdgeGraph ≤ S.actualEdgeGraph := by
  apply iSup_le
  intro e
  change GraphPath.actualEdgeGraph (S.pathAlongCopy f e) ≤ S.actualEdgeGraph
  dsimp only [pathAlongCopy]
  split_ifs
  · exact le_iSup (fun d => GraphPath.actualEdgeGraph (S.edgePath d)) (OrientedEdge.mapCopy f e)
  · rw [GraphPath.actualEdgeGraph_reverse]
    exact le_iSup (fun d => GraphPath.actualEdgeGraph (S.edgePath d)) (OrientedEdge.mapCopy f e)

theorem restrictCopy_edgePath_actualEdgeGraph {U : Type*} [Fintype U] [LinearOrder U]
    {F : SimpleGraph U} (S : GraphSubdivisionModel H G) (f : F.Copy H) (e : OrientedEdge F) :
    GraphPath.actualEdgeGraph ((S.restrictCopy f).edgePath e) =
      GraphPath.actualEdgeGraph (S.edgePath (OrientedEdge.mapCopy f e)) := by
  change GraphPath.actualEdgeGraph (S.pathAlongCopy f e) = _
  dsimp only [pathAlongCopy]
  split_ifs
  · rfl
  · exact GraphPath.actualEdgeGraph_reverse _

end GraphSubdivisionModel
end
end Erdos73

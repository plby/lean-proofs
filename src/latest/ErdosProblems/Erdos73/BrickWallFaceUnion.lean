import ErdosProblems.Erdos73.BrickFullEdgeCoverage
import ErdosProblems.Erdos73.BrickNetworkEdges

/-! The full rectangular face array equals the actual elementary-wall subdivision. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {c r : ℕ}

theorem exists_brickFace_oriented_edge (hc : 2 ≤ c) (hr : 2 ≤ r)
    (e : OrientedEdge (elementaryWall c r)) :
    ∃ i : Fin (r - 1) × Fin (c - 1), ∃ f : OrientedEdge (cycleGraph 6),
      OrientedEdge.mapCopy (brickFaceCopyAt i) f = e := by
  obtain ⟨a, j, u, v, huv, hu, hv⟩ := exists_brickFace_at_adj hc hr e.lo e.hi e.adj
  refine ⟨(a, j), OrientedEdge.ofAdj huv, ?_⟩
  apply OrientedEdge.eq_of_sym2_eq
  rw [OrientedEdge.mapCopy_sym2]
  rcases OrientedEdge.ofAdj_endpoints huv with hh | hh
  · rw [hh.1, hh.2, hu, hv]
  · rw [hh.1, hh.2, hu, hv, Sym2.eq_swap]

variable {V : Type*} {G : SimpleGraph V}

theorem brickWall_vertexSet_eq_faceUnion
    (S : GraphSubdivisionModel (elementaryWall c r) G) (hc : 2 ≤ c) (hr : 2 ≤ r) :
    S.vertexSet = Finset.univ.biUnion (brickFaceRegion S) := by
  ext x
  constructor
  · intro hx
    rcases (S.mem_vertexSet x).mp hx with ⟨w, hw⟩ | ⟨e, he⟩
    · obtain ⟨a, j, l, hl⟩ := exists_brickFace_at_vertex hc hr w
      refine mem_biUnion.mpr ⟨(a, j), mem_univ _, ?_⟩
      rw [← hw, ← hl]
      exact branch_mem_brickFaceSupport S _ _ _ _ _ l
    · obtain ⟨i, f, hf⟩ := exists_brickFace_oriented_edge hc hr e
      refine mem_biUnion.mpr ⟨i, mem_univ _, ?_⟩
      apply ((S.restrictCopy (brickFaceCopyAt i)).mem_vertexSet x).mpr
      apply Or.inr
      refine ⟨f, ?_⟩
      rw [S.restrictCopy_edgePath_vertexSet, hf]
      exact he
  · intro hx
    obtain ⟨i, _, hxi⟩ := mem_biUnion.mp hx
    exact brickFaceRegion_subset S i hxi

theorem brickWall_actualEdgeGraph_eq_faceUnion
    (S : GraphSubdivisionModel (elementaryWall c r) G) (hc : 2 ≤ c) (hr : 2 ≤ r) :
    S.actualEdgeGraph = ⨆ i : Fin (r - 1) × Fin (c - 1), brickFaceEdgeGraph S i := by
  apply le_antisymm
  · apply iSup_le
    intro e
    obtain ⟨i, f, hf⟩ := exists_brickFace_oriented_edge hc hr e
    rw [← hf, ← S.restrictCopy_edgePath_actualEdgeGraph]
    apply le_iSup_of_le i
    exact le_iSup (fun f => GraphPath.actualEdgeGraph
      ((S.restrictCopy (brickFaceCopyAt i)).edgePath f)) f
  · exact iSup_le (brickFaceEdgeGraph_le S)

theorem brickWall_vertexSet_robust_of_edges
    (S : GraphSubdivisionModel (elementaryWall c r) G) (hc : 2 ≤ c) (hr : 2 ≤ r)
    (J : SimpleGraph V) (hJ : S.actualEdgeGraph ≤ J) : DeletionOneConnected J S.vertexSet := by
  rw [brickWall_vertexSet_eq_faceUnion S hc hr]
  have : NeZero (r - 1) := ⟨by omega⟩
  have : NeZero (c - 1) := ⟨by omega⟩
  apply deletionOneConnected_biUnion (brickFaceRegion S)
    (fun i => brickFaceRegion_robust_in_graph S i J ((brickFaceEdgeGraph_le S i).trans hJ))
    ((show (pathGraph (r - 1)).Connected from ⟨pathGraph_preconnected _⟩).boxProd
      (show (pathGraph (c - 1)).Connected from ⟨pathGraph_preconnected _⟩))
  exact brickFaceRegion_adj_overlap S

end
end Erdos73

import ErdosProblems.Erdos73.SubdivisionEdgeGraph

/-! Restriction along composed copies preserves the same actual supports and edges. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset

variable {U W Z V : Type*} [Fintype U] [LinearOrder U] [Fintype W] [LinearOrder W]
variable [Fintype Z] [LinearOrder Z]
variable {F : SimpleGraph U} {H : SimpleGraph W} {K : SimpleGraph Z} {G : SimpleGraph V}

theorem OrientedEdge.mapCopy_comp (g : H.Copy K) (f : F.Copy H) (e : OrientedEdge F) :
    mapCopy g (mapCopy f e) = mapCopy (g.comp f) e := by
  apply eq_of_sym2_eq
  rw [mapCopy_sym2, mapCopy_sym2]
  rcases mapCopy_endpoints f e with he | he
  · rw [he.1, he.2]
    rfl
  · rw [he.1, he.2]
    exact Sym2.eq_swap

theorem GraphSubdivisionModel.restrictCopy_comp_vertexSet (S : GraphSubdivisionModel K G)
    (g : H.Copy K) (f : F.Copy H) :
    ((S.restrictCopy g).restrictCopy f).vertexSet = (S.restrictCopy (g.comp f)).vertexSet := by
  have hedge (e : OrientedEdge F) :
      (((S.restrictCopy g).restrictCopy f).edgePath e).vertexSet =
        ((S.restrictCopy (g.comp f)).edgePath e).vertexSet := by
    rw [(S.restrictCopy g).restrictCopy_edgePath_vertexSet,
      S.restrictCopy_edgePath_vertexSet, S.restrictCopy_edgePath_vertexSet,
      OrientedEdge.mapCopy_comp]
  ext x
  simp only [GraphSubdivisionModel.mem_vertexSet, GraphSubdivisionModel.restrictCopy_branchVertex,
    Copy.comp_apply, hedge]

theorem GraphSubdivisionModel.restrictCopy_comp_actualEdgeGraph (S : GraphSubdivisionModel K G)
    (g : H.Copy K) (f : F.Copy H) :
    ((S.restrictCopy g).restrictCopy f).actualEdgeGraph =
      (S.restrictCopy (g.comp f)).actualEdgeGraph := by
  apply iSup_congr
  intro e
  rw [(S.restrictCopy g).restrictCopy_edgePath_actualEdgeGraph,
    S.restrictCopy_edgePath_actualEdgeGraph, S.restrictCopy_edgePath_actualEdgeGraph,
    OrientedEdge.mapCopy_comp]

end
end Erdos73

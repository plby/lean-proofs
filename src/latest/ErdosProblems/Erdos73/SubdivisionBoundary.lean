import ErdosProblems.Erdos73.SubdivisionEdgeGraph

/-! A boundary of a union of whole corridors can leave only at a branch vertex. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {U W V : Type*} [Fintype U] [LinearOrder U] [Fintype W] [LinearOrder W]
variable {F : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V}

theorem branchVertex_mem_restrictCopy_iff (S : GraphSubdivisionModel H G) (f : F.Copy H) (w : W) :
    S.branchVertex w ∈ (S.restrictCopy f).vertexSet ↔ ∃ u : U, f u = w := by
  constructor
  · intro hw
    rcases ((S.restrictCopy f).mem_vertexSet _).mp hw with ⟨u, hu⟩ | ⟨e, he⟩
    · exact ⟨u, S.injective hu⟩
    · rw [S.restrictCopy_edgePath_vertexSet] at he
      have hh := S.branch_on_path (OrientedEdge.mapCopy f e) w he
      rw [OrientedEdge.mapCopy_endpoint_iff] at hh
      exact hh.elim (fun h => ⟨e.lo, h.symm⟩) (fun h => ⟨e.hi, h.symm⟩)
  · rintro ⟨u, rfl⟩
    exact ((S.restrictCopy f).mem_vertexSet _).mpr (Or.inl ⟨u, rfl⟩)

theorem branch_of_adj_leaving_restrictCopy (S : GraphSubdivisionModel H G) (f : F.Copy H)
    (T : Finset V) (hT : (S.restrictCopy f).vertexSet ⊆ T) {x y : V}
    (hx : x ∈ (S.restrictCopy f).vertexSet) (hxy : S.actualEdgeGraph.Adj x y) (hy : y ∉ T) :
    ∃ w : W, x = S.branchVertex w := by
  rcases ((S.restrictCopy f).mem_vertexSet x).mp hx with ⟨u, he⟩ | ⟨e, hxe⟩
  · exact ⟨f u, he.symm⟩
  · obtain ⟨d, hxy⟩ := SimpleGraph.iSup_adj.mp hxy
    have hends := Erdos73.GraphPath.actualEdgeGraph_adj_support (S.edgePath d) hxy
    rw [S.restrictCopy_edgePath_vertexSet] at hxe
    by_cases hed : OrientedEdge.mapCopy f e = d
    · apply (hy _).elim
      apply hT
      apply ((S.restrictCopy f).mem_vertexSet y).mpr
      apply Or.inr
      refine ⟨e, ?_⟩
      rw [S.restrictCopy_edgePath_vertexSet, hed]
      exact hends.2
    · obtain ⟨w, hxw, _, _⟩ := S.intersection hed x hxe hends.1
      exact ⟨w, hxw⟩

theorem neighbor_mem_restrictCopy_of_lifted_pattern_neighbors
    (S : GraphSubdivisionModel H G) (f : F.Copy H) (u : U)
    (hlift : ∀ z, H.Adj (f u) z → ∃ v : U, F.Adj u v ∧ f v = z)
    {y : V} (hxy : S.actualEdgeGraph.Adj (S.branchVertex (f u)) y) :
    y ∈ (S.restrictCopy f).vertexSet := by
  obtain ⟨e, hxy⟩ := SimpleGraph.iSup_adj.mp hxy
  have hends := Erdos73.GraphPath.actualEdgeGraph_adj_support (S.edgePath e) hxy
  have hfu := S.branch_on_path e (f u) hends.1
  have hz : ∃ z : W, H.Adj (f u) z ∧ s(f u, z) = s(e.lo, e.hi) := by
    rcases hfu with he | he
    · refine ⟨e.hi, ?_, ?_⟩ <;> rw [he]
      · exact e.adj
    · refine ⟨e.lo, ?_, ?_⟩ <;> rw [he]
      · exact e.adj.symm
      · exact Sym2.eq_swap
  obtain ⟨z, huz, hze⟩ := hz
  obtain ⟨v, huv, hfv⟩ := hlift z huz
  have hmap : OrientedEdge.mapCopy f (OrientedEdge.ofAdj huv) = e := by
    apply OrientedEdge.eq_of_sym2_eq
    rw [OrientedEdge.mapCopy_sym2]
    rcases OrientedEdge.ofAdj_endpoints huv with hh | hh
    · rw [hh.1, hh.2, hfv]
      exact hze
    · rw [hh.1, hh.2, hfv, Sym2.eq_swap]
      exact hze
  apply ((S.restrictCopy f).mem_vertexSet y).mpr
  apply Or.inr
  refine ⟨OrientedEdge.ofAdj huv, ?_⟩
  rw [S.restrictCopy_edgePath_vertexSet, hmap]
  exact hends.2

end
end Erdos73.GraphSubdivisionModel

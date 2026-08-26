import ErdosProblems.Erdos73.SubdivisionAdjacentPaths

/-! Exact support of the subdivision corridors used by a pattern walk. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

def walkSupport (S : GraphSubdivisionModel H G) {u v : W} (p : H.Walk u v) : Finset V :=
  p.support.toFinset.image S.branchVertex ∪
    (Finset.univ.filter (fun e : OrientedEdge H => s(e.lo, e.hi) ∈ p.edges)).biUnion
      (fun e => (S.edgePath e).vertexSet)

theorem mem_walkSupport (S : GraphSubdivisionModel H G) {u v : W} (p : H.Walk u v) (x : V) :
    x ∈ S.walkSupport p ↔ (∃ w ∈ p.support, S.branchVertex w = x) ∨
      ∃ e : OrientedEdge H, s(e.lo, e.hi) ∈ p.edges ∧ x ∈ (S.edgePath e).vertexSet := by
  simp only [walkSupport, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]

theorem walkSupport_subset_supportOver (S : GraphSubdivisionModel H G) {u v : W}
    (p : H.Walk u v) : S.walkSupport p ⊆ S.supportOver p.support.toFinset := by
  intro x hx
  rcases (S.mem_walkSupport p x).mp hx with ⟨w, hw, he⟩ | ⟨e, he, hx⟩
  · exact (S.mem_supportOver _ x).mpr (Or.inl ⟨w, List.mem_toFinset.mpr hw, he⟩)
  · exact (S.mem_supportOver _ x).mpr (Or.inr ⟨e,
      List.mem_toFinset.mpr (p.fst_mem_support_of_mem_edges he),
      List.mem_toFinset.mpr (p.snd_mem_support_of_mem_edges he), hx⟩)

theorem walkSupport_nil (S : GraphSubdivisionModel H G) (u : W) :
    S.walkSupport (.nil : H.Walk u u) = {S.branchVertex u} := by
  ext x
  simp only [mem_walkSupport, Walk.support_nil, Walk.edges_nil, List.mem_singleton,
    List.not_mem_nil, false_and, exists_false, or_false, mem_singleton]
  exact ⟨fun ⟨w, hw, he⟩ => he.symm.trans (congrArg S.branchVertex hw),
    fun hx => ⟨u, rfl, hx.symm⟩⟩

theorem walkSupport_cons (S : GraphSubdivisionModel H G) {u v w : W}
    (h : H.Adj u v) (p : H.Walk v w) :
    S.walkSupport (p.cons h) = (S.pathAlongAdj h).vertexSet ∪ S.walkSupport p := by
  let e := OrientedEdge.ofAdj h
  have he : s(e.lo, e.hi) = s(u, v) := OrientedEdge.ofAdj_sym2 h
  have hE : (S.pathAlongAdj h).vertexSet = (S.edgePath e).vertexSet := S.pathAlongAdj_vertexSet h
  ext x
  constructor
  · intro hx
    rcases (S.mem_walkSupport (p.cons h) x).mp hx with ⟨a, ha, hax⟩ | ⟨d, hd, hxd⟩
    · rcases List.mem_cons.mp ha with rfl | ha
      · apply mem_union_left
        rw [← hax, ← S.pathAlongAdj_source h]
        exact (S.pathAlongAdj h).source_mem_vertexSet
      · exact mem_union_right _ ((S.mem_walkSupport p x).mpr (Or.inl ⟨a, ha, hax⟩))
    · rcases List.mem_cons.mp hd with hd | hd
      · have hde : d = e := OrientedEdge.eq_of_sym2_eq (hd.trans he.symm)
        exact mem_union_left _ (hE ▸ (hde ▸ hxd))
      · exact mem_union_right _ ((S.mem_walkSupport p x).mpr (Or.inr ⟨d, hd, hxd⟩))
  · intro hx
    rcases mem_union.mp hx with hx | hx
    · exact (S.mem_walkSupport (p.cons h) x).mpr
        (Or.inr ⟨e, List.mem_cons.mpr (Or.inl he), hE ▸ hx⟩)
    · rcases (S.mem_walkSupport p x).mp hx with ⟨a, ha, hax⟩ | ⟨d, hd, hxd⟩
      · exact (S.mem_walkSupport (p.cons h) x).mpr
          (Or.inl ⟨a, List.mem_cons_of_mem _ ha, hax⟩)
      · exact (S.mem_walkSupport (p.cons h) x).mpr
          (Or.inr ⟨d, List.mem_cons_of_mem _ hd, hxd⟩)

end
end Erdos73.GraphSubdivisionModel

import ErdosProblems.Erdos73.SubdivisionSupports

/-! Connected pattern regions have connected actual subdivision supports. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

theorem branch_mem_supportOver (S : GraphSubdivisionModel H G) {T : Finset W}
    {w : W} (hw : w ∈ T) : S.branchVertex w ∈ S.supportOver T :=
  (S.mem_supportOver T _).mpr (Or.inl ⟨w, hw, rfl⟩)

theorem edgePath_subset_supportOver (S : GraphSubdivisionModel H G) {T : Finset W}
    (e : OrientedEdge H) (he : e.lo ∈ T) (he' : e.hi ∈ T) :
    (S.edgePath e).vertexSet ⊆ S.supportOver T := fun _ hv =>
  (S.mem_supportOver T _).mpr (Or.inr ⟨e, he, he', hv⟩)

theorem path_reachable_in_superset (P : GraphPath G) {R : Finset V} (hPR : P.vertexSet ⊆ R)
    {x y : V} (hx : x ∈ P.vertexSet) (hy : y ∈ P.vertexSet) :
    (G.induce (R : Set V)).Reachable ⟨x, hPR hx⟩ ⟨y, hPR hy⟩ := by
  have hr := P.connected_induce_vertexSet ⟨x, hx⟩ ⟨y, hy⟩
  exact hr.map (G.induceHomOfLE (show (P.vertexSet : Set V) ⊆ (R : Set V) from hPR)).toHom

theorem adjacent_branches_reachable (S : GraphSubdivisionModel H G) {T : Finset W}
    {u v : W} (hu : u ∈ T) (hv : v ∈ T) (huv : H.Adj u v) :
    (G.induce (S.supportOver T : Set V)).Reachable
      ⟨S.branchVertex u, S.branch_mem_supportOver hu⟩
      ⟨S.branchVertex v, S.branch_mem_supportOver hv⟩ := by
  let e := OrientedEdge.ofAdj huv
  have he := OrientedEdge.ofAdj_endpoints huv
  have heT : e.lo ∈ T := he.elim (fun h => h.1 ▸ hu) (fun h => h.1 ▸ hv)
  have heT' : e.hi ∈ T := he.elim (fun h => h.2 ▸ hv) (fun h => h.2 ▸ hu)
  have hsub := S.edgePath_subset_supportOver e heT heT'
  have hlu : S.branchVertex e.lo ∈ (S.edgePath e).vertexSet := by
    rw [← S.source_eq]
    exact (S.edgePath e).source_mem_vertexSet
  have hlv : S.branchVertex e.hi ∈ (S.edgePath e).vertexSet := by
    rw [← S.target_eq]
    exact (S.edgePath e).target_mem_vertexSet
  have huP : S.branchVertex u ∈ (S.edgePath e).vertexSet :=
    he.elim (fun h => h.1 ▸ hlu) (fun h => h.2 ▸ hlv)
  have hvP : S.branchVertex v ∈ (S.edgePath e).vertexSet :=
    he.elim (fun h => h.2 ▸ hlv) (fun h => h.1 ▸ hlu)
  exact path_reachable_in_superset _ hsub huP hvP

theorem exists_reachable_branch (S : GraphSubdivisionModel H G) {T : Finset W}
    (x : {v : V // v ∈ S.supportOver T}) :
    ∃ w : {w : W // w ∈ T}, (G.induce (S.supportOver T : Set V)).Reachable x
      ⟨S.branchVertex w.val, S.branch_mem_supportOver w.property⟩ := by
  rcases (S.mem_supportOver T x.val).mp x.property with ⟨w, hw, he⟩ | ⟨e, he, he', hx⟩
  · refine ⟨⟨w, hw⟩, ?_⟩
    have hxe : x = ⟨S.branchVertex w, S.branch_mem_supportOver hw⟩ := Subtype.ext he.symm
    rw [hxe]
  · have hlo : S.branchVertex e.lo ∈ (S.edgePath e).vertexSet := by
      rw [← S.source_eq]
      exact (S.edgePath e).source_mem_vertexSet
    exact ⟨⟨e.lo, he⟩, path_reachable_in_superset _ (S.edgePath_subset_supportOver e he he') hx hlo⟩

theorem connected_supportOver (S : GraphSubdivisionModel H G) {T : Finset W}
    (hT : (H.induce (T : Set W)).Connected) :
    (G.induce (S.supportOver T : Set V)).Connected := by
  let b (w : {w : W // w ∈ T}) : {v : V // v ∈ S.supportOver T} :=
    ⟨S.branchVertex w.val, S.branch_mem_supportOver w.property⟩
  have hwalk : ∀ {u v : {w : W // w ∈ T}}, (H.induce (T : Set W)).Walk u v →
      (G.induce (S.supportOver T : Set V)).Reachable (b u) (b v) := by
    intro u v p
    induction p with
    | nil => exact Reachable.refl _
    | @cons u v w huv p ih =>
      exact (S.adjacent_branches_reachable u.property v.property huv).trans ih
  have hpre : (G.induce (S.supportOver T : Set V)).Preconnected := by
    intro x y
    obtain ⟨u, hxu⟩ := S.exists_reachable_branch x
    obtain ⟨v, hyv⟩ := S.exists_reachable_branch y
    obtain ⟨p⟩ := hT u v
    exact hxu.trans ((hwalk p).trans hyv.symm)
  obtain ⟨w⟩ := hT.nonempty
  let : Nonempty {v : V // v ∈ S.supportOver T} := ⟨b w⟩
  exact ⟨hpre⟩

end
end Erdos73.GraphSubdivisionModel

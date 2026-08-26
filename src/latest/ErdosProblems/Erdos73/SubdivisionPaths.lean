import ErdosProblems.Erdos73.SubdivisionWalkSupport

/-! Simple pattern paths expand to simple host paths with exactly the prescribed corridor support. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

theorem exists_path_with_walkSupport (S : GraphSubdivisionModel H G)
    {u v : W} (p : H.Walk u v) (hp : p.IsPath) :
    ∃ P : GraphPath G, P.source = S.branchVertex u ∧ P.target = S.branchVertex v ∧
      P.vertexSet = S.walkSupport p := by
  induction p with
  | @nil u =>
    exact ⟨GraphPath.refl G (S.branchVertex u), rfl, rfl,
      (GraphPath.refl_vertexSet _).trans (S.walkSupport_nil u).symm⟩
  | @cons u v w h p ih =>
    obtain ⟨hpp, hnot⟩ := (Walk.cons_isPath_iff h p).mp hp
    obtain ⟨Q, hQs, hQt, hQset⟩ := ih hpp
    let E := S.pathAlongAdj h
    have hjoin : E.target = Q.source := (S.pathAlongAdj_target h).trans hQs.symm
    have hinter : ∀ ⦃x⦄, x ∈ E.vertexSet → x ∈ Q.vertexSet → x = E.target := by
      intro x hxE hxQ
      have hxS : x ∈ S.supportOver p.support.toFinset :=
        S.walkSupport_subset_supportOver p (hQset ▸ hxQ)
      exact (S.pathAlongAdj_inter_supportOver h p.support.toFinset
        (fun hu => hnot (List.mem_toFinset.mp hu)) hxE hxS).trans
        (S.pathAlongAdj_target h).symm
    let R := E.appendWithEqOfInterSubsetTarget Q hjoin hinter
    refine ⟨R, S.pathAlongAdj_source h, hQt, ?_⟩
    rw [S.walkSupport_cons, ← hQset]
    apply Finset.Subset.antisymm
    · exact E.appendWithEq_vertexSet_subset Q hjoin
        (E.appendWithEq_isPath_of_inter_subset_target Q hjoin hinter)
    · exact union_subset
        (E.left_vertexSet_subset_appendWithEq Q hjoin
          (E.appendWithEq_isPath_of_inter_subset_target Q hjoin hinter))
        (E.right_vertexSet_subset_appendWithEq Q hjoin
          (E.appendWithEq_isPath_of_inter_subset_target Q hjoin hinter))

theorem length_le_of_walkSupport_subset (S : GraphSubdivisionModel H G)
    {u v : W} (p : H.Walk u v) (hp : p.IsPath) (P : GraphPath G)
    (hsub : S.walkSupport p ⊆ P.vertexSet) : p.length ≤ P.walk.length := by
  have hbranches : p.support.toFinset.image S.branchVertex ⊆ P.vertexSet := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hx
    exact hsub ((S.mem_walkSupport p _).mpr
      (Or.inl ⟨w, List.mem_toFinset.mp hw, rfl⟩))
  have hc := card_le_card hbranches
  rw [card_image_of_injective _ S.injective, List.toFinset_card_of_nodup hp.support_nodup,
    GraphPath.vertexSet, List.toFinset_card_of_nodup P.isPath.support_nodup,
    Walk.length_support, Walk.length_support] at hc
  omega

theorem corridor_inter_walkSupport (S : GraphSubdivisionModel H G) {u v w : W}
    (h : H.Adj u v) (p : H.Walk v w) (hn : s(u, v) ∉ p.edges)
    {x : V} (hxE : x ∈ (S.pathAlongAdj h).vertexSet) (hxP : x ∈ S.walkSupport p) :
    x = S.branchVertex u ∨ x = S.branchVertex v := by
  rw [S.pathAlongAdj_vertexSet] at hxE
  let e := OrientedEdge.ofAdj h
  have he := OrientedEdge.ofAdj_endpoints h
  have hend (a : W) (ha : a = e.lo ∨ a = e.hi) : a = u ∨ a = v := by
    rcases he with he | he <;> rcases ha with ha | ha
    · exact Or.inl (ha.trans he.1)
    · exact Or.inr (ha.trans he.2)
    · exact Or.inr (ha.trans he.1)
    · exact Or.inl (ha.trans he.2)
  rcases (S.mem_walkSupport p x).mp hxP with ⟨a, _, hax⟩ | ⟨d, hd, hxd⟩
  · rcases hend a (S.branch_on_path e a (hax ▸ hxE)) with rfl | rfl
    · exact Or.inl hax.symm
    · exact Or.inr hax.symm
  · have hed : e ≠ d := by
      intro hed
      have hh : s(e.lo, e.hi) ∈ p.edges := hed ▸ hd
      rw [OrientedEdge.ofAdj_sym2 h] at hh
      exact hn hh
    obtain ⟨a, hxa, hae, _⟩ := S.intersection hed x hxE hxd
    rcases hend a hae with rfl | rfl
    · exact Or.inl hxa
    · exact Or.inr hxa

end
end Erdos73.GraphSubdivisionModel

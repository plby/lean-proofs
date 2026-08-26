import ErdosProblems.Erdos73.ParityPendantGraph

/-! Attach the colour-one source leaf without repeating any vertex. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {T : Finset V} {c : V → Bool}

theorem attach_pendant_source (P : GraphPath (parityPendantGraph G T c))
    (v : V) (hv : v ∈ T) (hs : P.source = Sum.inl v) (hfresh : Sum.inr v ∉ P.vertexSet) :
    ∃ Q : GraphPath (parityPendantGraph G T c), Q.source = pendantTerminal c v ∧
      Q.target = P.target ∧ Q.walk.length = P.walk.length + (c v).toNat ∧
      Q.vertexSet ⊆ P.vertexSet ∪ {Sum.inr v} ∧
      Q.vertexSet.image pendantProjection ⊆ P.vertexSet.image pendantProjection := by
  cases hc : c v with
  | false =>
    exact ⟨P, by simpa only [pendantTerminal, hc, Bool.false_eq_true, ↓reduceIte] using hs,
      rfl, by simp [hc], subset_union_left, subset_rfl⟩
  | true =>
    have ha : (parityPendantGraph G T c).Adj (Sum.inr v) P.source :=
      (parityPendant_leaf_adj v _).mpr ⟨hs, hv, hc⟩
    let Q : GraphPath (parityPendantGraph G T c) :=
      ⟨Sum.inr v, P.target, P.walk.cons ha,
        P.isPath.cons (fun hh => hfresh (List.mem_toFinset.mpr hh))⟩
    have hsub : Q.vertexSet ⊆ P.vertexSet ∪ {Sum.inr v} := by
      intro x hx
      have hh : x = Sum.inr v ∨ x ∈ P.walk.support := by
        simpa only [Q, GraphPath.vertexSet, Walk.support_cons, List.mem_toFinset,
          List.mem_cons] using hx
      rcases hh with rfl | hh
      · exact mem_union_right _ (mem_singleton_self _)
      · exact mem_union_left _ (List.mem_toFinset.mpr hh)
    refine ⟨Q, by simp only [Q, pendantTerminal, hc, ↓reduceIte], rfl, ?_, hsub, ?_⟩
    · simp only [Q, Walk.length_cons, hc, Bool.toNat_true]
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      rcases mem_union.mp (hsub hy) with hy | hy
      · exact mem_image.mpr ⟨y, hy, rfl⟩
      · have he : y = Sum.inr v := mem_singleton.mp hy
        exact mem_image.mpr ⟨P.source, P.source_mem_vertexSet, by
          simp only [hs, he, pendantProjection, Sum.elim_inl, Sum.elim_inr, id_eq]⟩

end
end Erdos73

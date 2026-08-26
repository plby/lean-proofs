import ErdosProblems.Erdos73.ParityPendantGraph

/-! Remove the pendant endpoint edges, with an exact colour/length identity. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {T : Finset V} {c : V → Bool}

theorem trim_pendant_source (P : GraphPath (parityPendantGraph G T c))
    (hsource : P.source ∈ parityPendantTerminals T c)
    (hn : ∀ v, P.source = Sum.inr v → ¬ P.walk.Nil) :
    ∃ Q : GraphPath (parityPendantGraph G T c),
      Q.source = Sum.inl (pendantProjection P.source) ∧ Q.target = P.target ∧
      Q.vertexSet ⊆ P.vertexSet ∧
      Q.walk.length + (c (pendantProjection P.source)).toNat = P.walk.length := by
  have hcases : (∃ v, P.source = Sum.inl v) ∨ (∃ v, P.source = Sum.inr v) := by
    cases hs : P.source with
    | inl v => exact Or.inl ⟨v, rfl⟩
    | inr v => exact Or.inr ⟨v, rfl⟩
  rcases hcases with ⟨v, hs⟩ | ⟨v, hs⟩
  ·
    have hv : v ∈ T ∧ c v = false := (inl_mem_parityPendantTerminals T c v).mp (hs ▸ hsource)
    refine ⟨P, by simp only [hs, pendantProjection, Sum.elim_inl, id_eq], rfl, subset_rfl, ?_⟩
    simp only [hs, pendantProjection, Sum.elim_inl, id_eq, hv.2, Bool.toNat_false, Nat.add_zero]
  ·
    have hv : v ∈ T ∧ c v = true := (inr_mem_parityPendantTerminals T c v).mp (hs ▸ hsource)
    have hnil := hn v hs
    let Q : GraphPath (parityPendantGraph G T c) :=
      ⟨P.walk.snd, P.target, P.walk.tail, P.isPath.tail⟩
    have hadj : (parityPendantGraph G T c).Adj (Sum.inr v) P.walk.snd := by
      simpa only [hs] using P.walk.adj_snd hnil
    have he := ((parityPendant_leaf_adj v _).mp hadj).1
    refine ⟨Q, ?_, rfl, ?_, ?_⟩
    · simpa only [hs, pendantProjection, Sum.elim_inr, id_eq] using he
    · intro x hx
      have hh : x ∈ P.walk.tail.support := List.mem_toFinset.mp hx
      rw [Walk.support_tail_of_not_nil _ hnil] at hh
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail hh)
    · simpa only [hs, pendantProjection, Sum.elim_inr, id_eq, hv.2, Bool.toNat_true]
        using P.walk.length_tail_add_one hnil

end
end Erdos73

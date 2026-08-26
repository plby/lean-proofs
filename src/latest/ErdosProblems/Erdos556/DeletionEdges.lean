import ErdosProblems.Erdos556.Basic

/-!
# Edge loss under vertex deletion

All removed edges are covered by the incidence sets of the removed
vertices. This gives the coarse linear loss bound needed for reservoirs.
-/

namespace Erdos556

open SimpleGraph Finset

theorem edge_count_le_induce_compl_add_card_mul {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card ≤ (G.induce (S : Set V)ᶜ).edgeFinset.card +
      S.card * Fintype.card V := by
  classical
  let A := G.edgeFinset.filter (fun e => e.toFinset ⊆ Sᶜ)
  let B := S.biUnion (fun v => G.incidenceFinset v)
  have hcover : G.edgeFinset ⊆ A ∪ B := by
    intro e he
    by_cases h : e.toFinset ⊆ Sᶜ
    · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
    · obtain ⟨x, hxe, hx⟩ := not_subset.mp h
      have hxS : x ∈ S := by simpa only [mem_compl, not_not] using hx
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨x, hxS, ?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨he, by simpa using hxe⟩
  have hA : A.card = (G.induce (S : Set V)ᶜ).edgeFinset.card := by
    have h := congrArg Finset.card (G.map_edgeFinset_induce (s := (S : Set V)ᶜ))
    simp only [card_map] at h
    have heq : G.edgeFinset ∩ ((S : Set V)ᶜ).toFinset.sym2 = A := by
      simp [A, G.filter_edgeFinset_toFinset_subset]
    rw [heq] at h
    exact h.symm
  have hB : B.card ≤ S.card * Fintype.card V := by
    calc
      B.card ≤ ∑ v ∈ S, (G.incidenceFinset v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ S, Fintype.card V := by
        apply sum_le_sum
        intro v _
        rw [G.card_incidenceFinset_eq_degree]
        exact (G.degree_lt_card_verts v).le
      _ = S.card * Fintype.card V := by simp
  exact (card_le_card hcover).trans ((card_union_le A B).trans (by omega))

#print axioms edge_count_le_induce_compl_add_card_mul

end Erdos556

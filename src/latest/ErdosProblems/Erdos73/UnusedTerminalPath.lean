import ErdosProblems.Erdos73.PathCongestion

/-! Disjointness bounds the number of initial paths with an unavailable terminal. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

theorem exists_unused_terminal_path
    {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I] {G : SimpleGraph V}
    (P : I → GraphPath G) (N D : Finset V)
    (hends : ∀ i, (P i).source ∈ N ∧ (P i).target ∈ N)
    (hdis : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (used : Finset I) (hsize : (N \ D).card + used.card < Fintype.card I) :
    ∃ i, i ∉ used ∧ (P i).source ∈ D ∧ (P i).target ∈ D := by
  let bad := Finset.univ.filter (fun i => (P i).source ∉ D ∨ (P i).target ∉ D)
  have hhit : ∀ i ∈ bad, ∃ x ∈ (P i).vertexSet, x ∈ N \ D := by
    intro i hi
    rcases (mem_filter.mp hi).2 with hi | hi
    · exact ⟨(P i).source, (P i).source_mem_vertexSet, mem_sdiff.mpr ⟨(hends i).1, hi⟩⟩
    · exact ⟨(P i).target, (P i).target_mem_vertexSet, mem_sdiff.mpr ⟨(hends i).2, hi⟩⟩
  have hcong : ∀ x ∈ N \ D, (bad.filter (fun i => x ∈ (P i).vertexSet)).card ≤ 1 := by
    intro x _
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hn
    exact disjoint_left.mp (hdis hn) (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have hb : bad.card ≤ (N \ D).card := by
    simpa using card_le_mul_of_hits_with_congestion bad (fun i => (P i).vertexSet)
      (N \ D) 1 hhit hcong
  by_contra hn
  have hsub : Finset.univ ⊆ bad ∪ used := by
    intro i _
    by_cases hi : i ∈ used
    · exact mem_union_right _ hi
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      by_contra hgood
      push Not at hgood
      exact hn ⟨i, hi, hgood.1, hgood.2⟩
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_univ] at hh
  omega

end
end Erdos73

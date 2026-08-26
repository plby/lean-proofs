import ErdosProblems.Erdos19.Core

/-!
# Finite completion lemmas for the asymptotic EFL proof

These are unconditional finite combinatorial lemmas. In particular, the list
selection result below proves the Hall argument used to color a remaining star;
it does not assume an edge-coloring theorem.
-/

namespace Erdos19

/-- A family of lists has distinct representatives if every list has at least
`a` entries, each palette entry is forbidden at at most `a` indices, and the
palette is at least as large as the index set. -/
theorem exists_injective_mem_of_bounded_forbidden
    {I K : Type*} [Fintype I] [DecidableEq K]
    (P : Finset K) (L : I → Finset K) (a : ℕ)
    (hpalette : Fintype.card I ≤ P.card)
    (hlist : ∀ i, a ≤ (L i).card)
    (hforbidden : ∀ c ∈ P,
      ((Finset.univ : Finset I).filter fun i ↦ c ∉ L i).card ≤ a) :
    ∃ f : I → K, Function.Injective f ∧ ∀ i, f i ∈ L i := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective L).mp
  intro S
  by_cases hsmall : S.card ≤ a
  · by_cases hS : S.Nonempty
    · obtain ⟨i, hi⟩ := hS
      exact hsmall.trans ((hlist i).trans
        (Finset.card_le_card (Finset.subset_biUnion_of_mem L hi)))
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  · have hP : P ⊆ S.biUnion L := by
      intro c hc
      by_contra hnot
      have hsub : S ⊆ (Finset.univ : Finset I).filter fun i ↦ c ∉ L i := by
        intro i hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
        intro hci
        exact hnot (Finset.mem_biUnion.mpr ⟨i, hi, hci⟩)
      exact hsmall ((Finset.card_le_card hsub).trans (hforbidden c hc))
    exact (Finset.card_le_univ S).trans
      (hpalette.trans (Finset.card_le_card hP))

#print axioms exists_injective_mem_of_bounded_forbidden

end Erdos19

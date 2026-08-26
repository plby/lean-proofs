import ErdosProblems.Erdos556.ProfileSaturation
import ErdosProblems.Erdos556.CoreCleaning
import ErdosProblems.Erdos556.BipartiteDefect

/-! A single deletion set cleans all uniquely separated profile pairs at once. -/

namespace Erdos556

open SimpleGraph Finset

theorem ThreeColourDecomposition.exists_profile_cleaning {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (d : ℕ) :
    ∃ Z : Finset V, d * Z.card ≤ 2 * Nat.card h.potentialMissing.edgeSet ∧
      ∀ p q : CubeProfile, ∀ i : Fin 3, uniqueProfileSeparator p q i →
        BipartiteDefect (c.graph i) (h.profileClass p \ Z) (h.profileClass q \ Z) d := by
  classical
  obtain ⟨K, _, hcount, hclean⟩ := exists_clean_core h.potentialMissing univ d
  let Z : Finset V := univ \ K
  have hZ : Z.card = Fintype.card V - K.card := by simp [Z, card_sdiff]
  have he : Nat.card (h.potentialMissing.induce ((univ : Finset V) : Set V)).edgeSet =
      Nat.card h.potentialMissing.edgeSet := by
    have hsupp : h.potentialMissing.support ⊆ ((univ : Finset V) : Set V) :=
      fun _ _ => mem_univ _
    have hh := h.potentialMissing.card_edgeFinset_induce_of_support_subset hsupp
    simpa only [edgeFinset_card_eq_natCard_edgeSet] using hh
  have hc : d * Z.card ≤ 2 * Nat.card h.potentialMissing.edgeSet := by
    simp only [edgeFinset_card_eq_natCard_edgeSet, card_univ] at hcount
    rw [he] at hcount
    rwa [hZ]
  refine ⟨Z, hc, ?_⟩
  intro p q i hsep
  have hK {x : V} (hx : x ∉ Z) : x ∈ K := by simpa [Z] using hx
  constructor
  · intro x hx
    have hxK := hK (mem_sdiff.mp hx).2
    have hsub : ((h.profileClass q \ Z).filter (fun y => ¬ (c.graph i).Adj x y)) ⊆
        h.potentialMissing.neighborFinset x ∩ univ := by
      intro y hy
      obtain ⟨hy, hxy⟩ := mem_filter.mp hy
      exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr
        (h.wrong_colour_unique_separator_missing p q i hsep x y
          (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hxy), mem_univ _⟩
    exact (card_le_card hsub).trans (hclean x hxK)
  · intro y hy
    have hyK := hK (mem_sdiff.mp hy).2
    have hsub : ((h.profileClass p \ Z).filter (fun x => ¬ (c.graph i).Adj y x)) ⊆
        h.potentialMissing.neighborFinset y ∩ univ := by
      intro x hx
      obtain ⟨hx, hyx⟩ := mem_filter.mp hx
      have hxy : ¬ (c.graph i).Adj x y := fun hxy => hyx hxy.symm
      exact mem_inter.mpr ⟨(mem_neighborFinset _ _ _).mpr
        (h.wrong_colour_unique_separator_missing p q i hsep x y
          (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 hxy).symm, mem_univ _⟩
    exact (card_le_card hsub).trans (hclean y hyK)

#print axioms ThreeColourDecomposition.exists_profile_cleaning

end Erdos556

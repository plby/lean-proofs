import ErdosProblems.Erdos556.DecompositionEdges

/-!
# Separations of order at most one

Every graph of order at least three which is not two-connected has a
separation with two nonempty sides and at most one separating vertex.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_small_separation_of_not_twoConnected {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : ¬ TwoConnected G) :
    ∃ A B S : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Disjoint A S ∧ Disjoint B S ∧ A ∪ B ∪ S = univ ∧ S.card ≤ 1 ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
  classical
  have hex : ∃ S : Finset V, S.card ≤ 1 ∧ ¬ (G.induce (S : Set V)ᶜ).Preconnected := by
    by_cases hc : G.Connected
    · have hv : ∃ v : V, ¬ (G.induce ({v}ᶜ : Set V)).Connected := by
        by_contra! h
        exact hG ⟨hcard, hc, h⟩
      obtain ⟨v, hv⟩ := hv
      refine ⟨{v}, by simp, ?_⟩
      rw [Finset.coe_singleton]
      intro hp
      have hn : 0 < Fintype.card ({v}ᶜ : Set V) := by
        rw [Fintype.card_compl_set, Set.card_singleton]
        omega
      letI : Nonempty ({v}ᶜ : Set V) := Fintype.card_pos_iff.mp hn
      exact hv ⟨hp⟩
    · refine ⟨∅, by simp, ?_⟩
      rw [Finset.coe_empty, Set.compl_empty]
      intro hp
      letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      exact hc ⟨(G.induceUnivIso.preconnected_iff).mp hp⟩
  obtain ⟨S, hS, hdisc⟩ := hex
  obtain ⟨A, B, hA, hB, hAB, hAS, hBS, hcover, hcross⟩ :=
    exists_separation_of_not_preconnected G S hdisc
  exact ⟨A, B, S, hA, hB, hAB, hAS, hBS, hcover, hS, hcross⟩

theorem card_sum_of_separation {V : Type*} [Fintype V] [DecidableEq V]
    (A B S : Finset V) (hAB : Disjoint A B) (hAS : Disjoint A S)
    (hBS : Disjoint B S) (hcover : A ∪ B ∪ S = univ) :
    A.card + B.card + S.card = Fintype.card V := by
  have h := congrArg Finset.card hcover
  rwa [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAS, hBS⟩),
    card_union_of_disjoint hAB, card_univ] at h

#print axioms exists_small_separation_of_not_twoConnected

end Erdos556

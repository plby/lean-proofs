import ErdosProblems.Erdos1105.SeparatedRepresentative

namespace Erdos1105

open SimpleGraph Finset

theorem component_card_lt_delete_bridge {V : Type*} [Fintype V] (G : SimpleGraph V)
    {e : Sym2 V} (he : e ∈ G.edgeSet) (hb : G.IsBridge e) :
    Nat.card G.ConnectedComponent < Nat.card (G.deleteEdges {e}).ConnectedComponent := by
  classical
  let D := G.deleteEdges {e}
  let f : D.ConnectedComponent → G.ConnectedComponent := ConnectedComponent.map (Hom.ofLE (deleteEdges_le _))
  have hf : Function.Surjective f := ConnectedComponent.surjective_map_ofLE (deleteEdges_le _)
  have hninj : ¬Function.Injective f := by
    intro hinj
    induction e using Sym2.inductionOn with
    | _ a b =>
      have he' : G.Adj a b := he
      have heq : f (D.connectedComponentMk a) = f (D.connectedComponentMk b) :=
        ConnectedComponent.sound he'.reachable
      exact (isBridge_iff.mp hb) (ConnectedComponent.exact (hinj heq))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply lt_of_le_of_ne (Fintype.card_le_of_surjective f hf)
  intro heq
  exact hninj ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, heq.symm⟩).1

/-- Removing only bridges pays for at least one new component per
removed edge. The inequality form suffices for the extremal argument. -/
theorem bridge_deletion_budget {V : Type*} [Fintype V] (R H : SimpleGraph V)
    (hle : H ≤ R) (hbridge : ∀ e ∈ R.edgeSet, e ∉ H.edgeSet → R.IsBridge e) :
    Nat.card R.edgeSet + Nat.card R.ConnectedComponent ≤
      Nat.card H.edgeSet + Nat.card H.ConnectedComponent := by
  classical
  induction hsize : Nat.card R.edgeSet using Nat.strong_induction_on generalizing R with
  | h n ih =>
    by_cases heq : R = H
    · subst R
      omega
    · have hex : ∃ e ∈ R.edgeSet, e ∉ H.edgeSet := by
        by_contra h
        push Not at h
        exact heq (le_antisymm (edgeSet_subset_edgeSet.mp h) hle)
      obtain ⟨e, he, heH⟩ := hex
      let D := R.deleteEdges {e}
      have hHD : H ≤ D := by
        intro a b hab
        apply deleteEdges_adj.mpr
        exact ⟨hle hab, fun heq ↦ heH (heq ▸ hab)⟩
      have hDbridge : ∀ f ∈ D.edgeSet, f ∉ H.edgeSet → D.IsBridge f :=
        fun f hf hnot ↦ SimpleGraph.IsBridge.anti (deleteEdges_le _)
          (hbridge f (edgeSet_mono (deleteEdges_le _) hf) hnot)
      have hcard : D.edgeFinset.card + 1 = R.edgeFinset.card := by
        have hdel : D.edgeFinset = R.edgeFinset.erase e := by
          ext f
          simp only [D, mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff,
            Set.mem_singleton_iff, mem_erase]
          tauto
        rw [hdel, card_erase_add_one (mem_edgeFinset.mpr he)]
      have hcard' : Nat.card D.edgeSet + 1 = Nat.card R.edgeSet := by
        simpa only [Nat.card_eq_fintype_card, edgeFinset_card] using hcard
      have hlt : Nat.card D.edgeSet < n := by omega
      have hbound := ih _ hlt D hHD hDbridge rfl
      have hcomp := component_card_lt_delete_bridge R he (hbridge e he heH)
      change Nat.card R.ConnectedComponent < Nat.card D.ConnectedComponent at hcomp
      omega

end Erdos1105

#print axioms Erdos1105.bridge_deletion_budget

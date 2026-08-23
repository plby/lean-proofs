import ErdosProblems.Erdos1105.MaxComponentGood

namespace Erdos1105

open SimpleGraph Finset

lemma choose_two_split_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    a.choose 2 + b.choose 2 ≤ (a + b - 1).choose 2 := by
  have h : (a.choose 2 : ℚ) + b.choose 2 ≤ ((a + b - 1).choose 2 : ℕ) := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two,
      Nat.cast_sub (by omega : 1 ≤ a + b), Nat.cast_add, Nat.cast_one]
    have ha' : (1 : ℚ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℚ) ≤ b := by exact_mod_cast hb
    have hm := mul_nonneg (sub_nonneg.mpr ha') (sub_nonneg.mpr hb')
    nlinarith
  exact_mod_cast h

theorem closed_cut_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V)
    (hclosed : ∀ a b, G.Adj a b → (a ∈ S ↔ b ∈ S)) :
    Nat.card G.edgeSet ≤ S.card.choose 2 + Sᶜ.card.choose 2 := by
  classical
  have hcut := E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_compl G S hclosed
  have hS := (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
  have hT := (G.induce (↑(Sᶜ) : Set V)).card_edgeFinset_le_card_choose_two
  have hcS : Fintype.card (S : Set V) = S.card :=
    Fintype.card_of_finset' S (fun _ ↦ Iff.rfl)
  have hcT : Fintype.card (↑(Sᶜ) : Set V) = Sᶜ.card :=
    Fintype.card_of_finset' Sᶜ (fun _ ↦ Iff.rfl)
  rw [hcS] at hS
  rw [hcT] at hT
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card]
  omega

theorem disconnected_edge_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : ¬G.Preconnected) : Nat.card G.edgeSet ≤ (Fintype.card V - 1).choose 2 := by
  classical
  have hex : ∃ a b, ¬G.Reachable a b := by simpa only [Preconnected, not_forall] using hconn
  obtain ⟨a, b, hab⟩ := hex
  obtain ⟨S, hS, ha⟩ := exists_graphComponent G a
  have hb : b ∉ S := fun hb ↦ hab (hS.reachable ha hb)
  have hbound := closed_cut_edge_bound G S
    (fun x y hxy ↦ ⟨fun hx ↦ hS.closed x hx y hxy, fun hy ↦ hS.closed y hy x hxy.symm⟩)
  have hc := choose_two_split_le hS.nonempty.card_pos
    (card_pos.mpr (show Sᶜ.Nonempty from ⟨b, mem_compl.mpr hb⟩))
  have hsum : S.card + Sᶜ.card = Fintype.card V := by
    rw [card_compl]
    exact Nat.add_sub_of_le S.card_le_univ
  rw [hsum] at hc
  exact hbound.trans hc

theorem bridge_edge_bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    {e : Sym2 V} (he : e ∈ G.edgeSet) (hb : G.IsBridge e) :
    Nat.card G.edgeSet ≤ (Fintype.card V - 1).choose 2 + 1 := by
  classical
  let D := G.deleteEdges {e}
  have hdis : ¬D.Preconnected := by
    intro hconn
    induction e using Sym2.inductionOn with
    | _ a b => exact (isBridge_iff.mp hb) (hconn a b)
  have hbound := disconnected_edge_bound D hdis
  have hdel : D.edgeFinset = G.edgeFinset.erase e := by
    ext f
    simp only [D, mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff,
      Set.mem_singleton_iff, mem_erase]
    tauto
  have hcard : Nat.card D.edgeSet + 1 = Nat.card G.edgeSet := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, ← edgeFinset_card,
      hdel, card_erase_add_one (mem_edgeFinset.mpr he)]
  omega

end Erdos1105

#print axioms Erdos1105.bridge_edge_bound

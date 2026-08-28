import ErdosProblems.Erdos577.AlmostComplete

/-! Recognize complete induced vertex sets from their maximum possible edge count. -/

namespace Erdos577

open Finset

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

lemma isClique_of_choose_le_edgeCount {s : Finset V} (h : s.card.choose 2 ≤ edgeCount G s) :
    G.IsClique s := by
  classical
  by_contra hn
  have hne : G.induce (s : Set V) ≠ ⊤ := fun he ↦ hn (G.induce_eq_top.mp he)
  have hlt := card_lt_card ((SimpleGraph.edgeFinset_ssubset_edgeFinset).mpr
    (lt_top_iff_ne_top.mpr hne))
  have htop : (⊤ : SimpleGraph (s : Set V)).edgeFinset.card = s.card.choose 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    change (Fintype.card s).choose 2 = s.card.choose 2
    rw [Fintype.card_coe]
  change edgeCount G s < (⊤ : SimpleGraph (s : Set V)).edgeFinset.card at hlt
  rw [htop] at hlt
  omega

lemma edgeCount_eq_choose_iff {s : Finset V} : edgeCount G s = s.card.choose 2 ↔ G.IsClique s :=
  ⟨fun h ↦ isClique_of_choose_le_edgeCount h.ge, edgeCount_clique⟩

lemma clique_of_four_six {s : Finset V} (hs : s.card = 4) (he : edgeCount G s = 6) :
    G.IsNClique 4 s := by
  refine ⟨isClique_of_choose_le_edgeCount ?_, hs⟩
  rw [hs, he]
  decide

variable [DecidableEq V]

lemma four_set_edgeCount_le_three {s : Finset V} (hs : s.card = 4)
    (hq : ¬QuadOn G s) (ht : ¬TriangleIn G s) : edgeCount G s ≤ 3 := by
  have hv : ∃ v ∈ s, degreeIn G v s ≤ 1 := by
    by_contra hn
    apply hq (QuadOn.of_degreeIn hs ?_)
    intro v hv
    have hnot : ¬degreeIn G v s ≤ 1 := fun h ↦ hn ⟨v, hv, h⟩
    omega
  obtain ⟨v, hv, hd⟩ := hv
  by_contra hn
  have hsplit := edgeCount_erase_add G v hv
  have he : 3 ≤ edgeCount G (s.erase v) := by omega
  have hcard : (s.erase v).card = 3 := by rw [card_erase_of_mem hv, hs]
  have hc : G.IsNClique 3 (s.erase v) := by
    refine ⟨isClique_of_choose_le_edgeCount ?_, hcard⟩
    simpa only [hcard, Nat.choose] using he
  exact ht ⟨s.erase v, erase_subset v s, hc⟩

end Erdos577

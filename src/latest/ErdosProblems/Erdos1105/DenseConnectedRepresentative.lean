import ErdosProblems.Erdos1105.DisconnectedEdges

namespace Erdos1105

open SimpleGraph Finset

theorem ColorRepresentative.card_eq {V C : Type*} [Fintype V]
    {G R Q : SimpleGraph V} {c : Sym2 V → C}
    (hR : ColorRepresentative G c R) (hQ : ColorRepresentative G c Q) :
    Nat.card R.edgeSet = Nat.card Q.edgeSet := by
  classical
  have hle {R Q : SimpleGraph V} (hR : ColorRepresentative G c R)
      (hQ : ColorRepresentative G c Q) : Nat.card R.edgeSet ≤ Nat.card Q.edgeSet := by
    have hp : ∀ e : R.edgeSet, ∃ f ∈ Q.edgeSet, c f = c e.val :=
      fun e ↦ hQ.palette e.val (edgeSet_mono hR.le e.property)
    choose f hf hc using hp
    let φ : R.edgeSet → Q.edgeSet := fun e ↦ ⟨f e, hf e⟩
    apply Nat.card_le_card_of_injective φ
    intro e d hed
    apply Subtype.ext
    apply hR.rainbow e.property d.property
    exact (hc e).symm.trans ((congrArg c (congrArg Subtype.val hed)).trans (hc d))
  exact le_antisymm (hle hR hQ) (hle hQ hR)

theorem MaxRepresentativeComponent.cross_color_count_bound {V C : Type*}
    [Fintype V] [DecidableEq V] {G R : SimpleGraph V} {c : Sym2 V → C} {S : Finset V}
    (hmax : MaxRepresentativeComponent G c R S) {a b : V}
    (ha : a ∈ S) (hb : b ∉ S) (hab : G.Adj a b) :
    Nat.card R.edgeSet ≤ (Fintype.card V - 2).choose 2 + 1 := by
  classical
  obtain ⟨e, he, hc⟩ := hmax.representative.palette s(a, b) hab
  have heS := hmax.cross_internal hmax.representative hmax.component ha hb hab ⟨e, he⟩ hc
  have hebridge := hmax.cross_bridge hmax.representative hmax.component ha hb hab ⟨e, he⟩ hc
  have hinside : Nat.card (R.induce (S : Set V)).edgeSet ≤ (S.card - 1).choose 2 + 1 := by
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hx, hy⟩ := pair_toFinset_subset.mp heS
      have hb' := isBridge_induce_of_isBridge R (S : Set V) s(⟨x, hx⟩, ⟨y, hy⟩) hebridge
      have hbound := bridge_edge_bound (R.induce (S : Set V)) he hb'
      have hcard : Fintype.card (S : Set V) = S.card :=
        Fintype.card_of_finset' S (fun _ ↦ Iff.rfl)
      simpa only [hcard] using hbound
  have hS₂ : 2 ≤ S.card := by
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hx, hy⟩ := pair_toFinset_subset.mp heS
      have hxy : R.Adj x y := he
      have hle : ({x, y} : Finset V) ⊆ S :=
        Finset.insert_subset_iff.mpr ⟨hx, Finset.singleton_subset_iff.mpr hy⟩
      have h := card_le_card hle
      simpa only [card_pair hxy.ne] using h
  have houtside : Nat.card (R.induce (↑(Sᶜ) : Set V)).edgeSet ≤ Sᶜ.card.choose 2 := by
    have h := (R.induce (↑(Sᶜ) : Set V)).card_edgeFinset_le_card_choose_two
    have hcard : Fintype.card (↑(Sᶜ) : Set V) = Sᶜ.card :=
      Fintype.card_of_finset' Sᶜ (fun _ ↦ Iff.rfl)
    rw [hcard] at h
    simpa only [Nat.card_eq_fintype_card, edgeFinset_card] using h
  have hcut := E767EGApi.card_edgeFinset_eq_card_induce_add_card_induce_compl R S
    (fun x y hxy ↦ ⟨fun hx ↦ hmax.component.closed x hx y hxy,
      fun hy ↦ hmax.component.closed y hy x hxy.symm⟩)
  have hcut' : Nat.card R.edgeSet = Nat.card (R.induce (S : Set V)).edgeSet +
      Nat.card (R.induce (↑(Sᶜ) : Set V)).edgeSet := by
    simpa only [Nat.card_eq_fintype_card, edgeFinset_card] using hcut
  have hTpos : 0 < Sᶜ.card := card_pos.mpr ⟨b, mem_compl.mpr hb⟩
  have hchoose := choose_two_split_le (show 0 < S.card - 1 by omega) hTpos
  have hsum : S.card - 1 + Sᶜ.card - 1 = Fintype.card V - 2 := by
    have hle := S.card_le_univ
    rw [card_compl]
    omega
  rw [hsum] at hchoose
  omega

/-- A complete-graph coloring using more than `choose(n-2,2)+1`
colors always has a connected full representative. This is the
boundary case needed before any vertex-deletion induction. -/
theorem exists_connected_representative_of_dense {V C : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (c : Sym2 V → C) {R : SimpleGraph V}
    (hR : ColorRepresentative ⊤ c R)
    (hcount : (Fintype.card V - 2).choose 2 + 1 < Nat.card R.edgeSet) :
    ∃ Q, ColorRepresentative ⊤ c Q ∧ Q.Preconnected := by
  classical
  obtain ⟨Q, S, hmax⟩ := exists_maxRepresentativeComponent (⊤ : SimpleGraph V) c
  have hcard := hR.card_eq hmax.representative
  refine ⟨Q, hmax.representative, ?_⟩
  have hfull : S = univ := by
    by_contra hne
    have hex : ∃ b, b ∉ S := by
      by_contra h
      push Not at h
      exact hne (Finset.eq_univ_of_forall h)
    obtain ⟨b, hb⟩ := hex
    obtain ⟨a, ha⟩ := hmax.component.nonempty
    have hab : a ≠ b := fun h ↦ hb (h ▸ ha)
    have hbound := hmax.cross_color_count_bound ha hb (by simpa using hab)
    omega
  intro a b
  apply hmax.component.reachable
  · simp [hfull]
  · simp [hfull]

end Erdos1105

#print axioms Erdos1105.exists_connected_representative_of_dense

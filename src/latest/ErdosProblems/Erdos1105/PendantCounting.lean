import ErdosProblems.Erdos1105.ConnectedPathStability
import ErdosProblems.Erdos1105.PathNeighborCounts

namespace Erdos1105

open SimpleGraph Finset

theorem pendant_edges_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {u : V}
    (hpend : ∀ x ∉ S, ∀ y, G.Adj x y → y = u) :
    G.edgeFinset.card ≤ (E767EGApi.edgesInside G S).card + (Fintype.card V - S.card) := by
  classical
  have hsub : G.edgeFinset ⊆ E767EGApi.edgesInside G S ∪
      Sᶜ.image (fun v ↦ s(v, u)) := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      by_cases ha : a ∈ S
      · by_cases hb : b ∈ S
        · apply mem_union_left
          apply mem_filter.mpr
          refine ⟨he, ?_⟩
          intro v hv
          have hv : v = a ∨ v = b := by simpa using hv
          exact hv.elim (fun h ↦ h ▸ ha) (fun h ↦ h ▸ hb)
        · have hau := hpend b hb a hab.symm
          apply mem_union_right
          exact mem_image.mpr ⟨b, mem_compl.mpr hb, by rw [hau, Sym2.eq_swap]⟩
      · have hbu := hpend a ha b hab
        apply mem_union_right
        exact mem_image.mpr ⟨a, mem_compl.mpr ha, by rw [hbu]⟩
  calc
    _ ≤ (E767EGApi.edgesInside G S ∪ Sᶜ.image (fun v ↦ s(v, u))).card := card_le_card hsub
    _ ≤ (E767EGApi.edgesInside G S).card + (Sᶜ.image (fun v ↦ s(v, u))).card := card_union_le _ _
    _ ≤ (E767EGApi.edgesInside G S).card + Sᶜ.card := Nat.add_le_add_left (card_image_le) _
    _ = _ := by rw [card_compl]

theorem pendant_core_degree_lower {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {u : V}
    (hpend : ∀ x ∉ S, ∀ y, G.Adj x y → y = u)
    (hedges : S.card.choose 2 + 2 ≤ G.edgeFinset.card)
    {v : V} (hv : v ∈ S) :
    S.card + 1 ≤ degreeWithin G S v + (Fintype.card V - S.card) := by
  have he := pendant_edges_le G S hpend
  rw [edgesInside_erase G hv] at he
  have hc := edgesInside_le_choose G (S.erase v)
  rw [card_erase_of_mem hv] at hc
  have hpos := card_pos.mpr ⟨v, hv⟩
  have hpred : S.card - 1 + 1 = S.card := by omega
  have hchoose := Nat.choose_succ_succ (S.card - 1) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, hpred, Nat.choose_one_right] at hchoose
  omega

theorem PendantCliqueShape.edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hshape : PendantCliqueShape G k) (hk : 2 ≤ k) (hn : k ≤ Fintype.card V) :
    G.edgeFinset.card ≤ pathExtremalEdges (Fintype.card V) (k - 1) 1 := by
  obtain ⟨S, hS, u, _, hpend⟩ := hshape
  have h := (pendant_edges_le G S hpend).trans
    (Nat.add_le_add_right (edgesInside_le_choose G S) _)
  rw [hS] at h
  have h₁ : k - 1 - 1 = k - 2 := by omega
  have h₂ : Fintype.card V - (k - 1) + 1 = Fintype.card V - (k - 2) := by omega
  simpa only [pathExtremalEdges, h₁, h₂, one_mul] using h

lemma pendant_outside_degree_le_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {u : V}
    (hpend : ∀ x ∉ S, ∀ y, G.Adj x y → y = u) {x : V} (hx : x ∉ S) : G.degree x ≤ 1 := by
  classical
  have hsub : G.neighborFinset x ⊆ {u} := by
    intro y hy
    exact mem_singleton.mpr (hpend x hx y (by simpa using hy))
  simpa using card_le_card hsub

lemma not_pendantShape_of_many_degree_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (S : Finset V) (hS : S.card = k - 2) (hdeg : ∀ v ∈ S, 2 ≤ G.degree v)
    {x : V} (hx : x ∉ S) (hxdeg : 2 ≤ G.degree x) : ¬PendantCliqueShape G k := by
  classical
  rintro ⟨T, hT, u, hu, hpend⟩
  have hsub : insert x S ⊆ T := by
    intro v hv
    have hdeg' : 2 ≤ G.degree v := (mem_insert.mp hv).elim (fun h ↦ h ▸ hxdeg) (hdeg v)
    by_contra hvT
    have := pendant_outside_degree_le_one G T hpend hvT
    omega
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hx, hS, hT] at hcard
  omega

lemma degreeWithin_delete_edge_lower {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (v : V) (e : Sym2 V) :
    degreeWithin G S v ≤ degreeWithin (G.deleteEdges {e}) S v + 1 := by
  classical
  let A := S.filter (G.Adj v)
  let B := S.filter ((G.deleteEdges {e}).Adj v)
  have hBA : B ⊆ A := by
    intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).1, (deleteEdges_adj.mp (mem_filter.mp hw).2).1⟩
  have hlost (w : V) (hw : w ∈ A \ B) : s(v, w) = e := by
    have hwA := mem_filter.mp (mem_sdiff.mp hw).1
    by_contra hne
    exact (mem_sdiff.mp hw).2 (mem_filter.mpr ⟨hwA.1, deleteEdges_adj.mpr ⟨hwA.2, hne⟩⟩)
  have hcard : (A \ B).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have heq := (hlost a ha).trans (hlost b hb).symm
    rcases Sym2.eq_iff.mp heq with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hsum := card_sdiff_add_card_eq_card hBA
  have hA : degreeWithin G S v = A.card := by
    unfold degreeWithin
    apply congrArg Finset.card
    ext w
    simp [A]
  have hB : degreeWithin (G.deleteEdges {e}) S v = B.card := by
    unfold degreeWithin
    apply congrArg Finset.card
    ext w
    simp [B]
  omega

end Erdos1105

#print axioms Erdos1105.pendant_core_degree_lower
#print axioms Erdos1105.degreeWithin_delete_edge_lower

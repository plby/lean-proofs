import ErdosProblems.Erdos577.TripleLowFactors

/-! A third row of size one forces two center neighbors and four actual block labels. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {q : Quadrilateral G} {a : Finset V}

theorem LowCore.center_two_of_third_one (h : LowCore c p q a) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) (hthird : degreeIn G (p.vertices 3) a = 1) :
    2 ≤ degreeIn G p.center a := by
  have hb : degreeIn G (p.vertices 2) a ≤ 1 := by
    by_contra hlarge
    obtain ⟨_, _, hp⟩ := hc.three_leaf_preparation hcard hdeg hn p h.paw h.core_block
      h.leaf_three (by omega)
    rcases hp with ⟨_, hz⟩ | ⟨he, _⟩
    · have hzero : degreeIn G (p.vertices 3) a = 0 := by
        change (a.filter (G.Adj (p.vertices 3))).card = 0
        rw [hz, card_empty]
      omega
    · have hthree : degreeIn G (p.vertices 3) a = 3 :=
        (congrArg Finset.card he).trans h.leaf_three
      omega
  have he := p.contacts_triangle a
  rw [h.triangle_four] at he
  change 4 = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at he
  omega

theorem LowCore.third_one_labels (h : LowCore c p q a) (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ z, 2 * k ≤ G.degree z)
    (hn : ¬HasPacking G k) (hthird : degreeIn G (p.vertices 3) a = 1) :
    ∃ z v s t : V, a = {z, v, s, t} ∧ z ∈ a ∧ v ∈ a ∧ s ∈ a ∧ t ∈ a ∧
      G.Adj (p.vertices 3) z ∧ G.Adj p.center v ∧ G.Adj p.leaf v ∧
      G.Adj p.leaf s ∧ G.Adj p.leaf t ∧ ¬G.Adj p.leaf z ∧ s ≠ t := by
  have hr := h.center_two_of_third_one hc hcard hdeg hn hthird
  have hzcard : (a.filter (G.Adj (p.vertices 3))).card = 1 := hthird
  obtain ⟨z, hz⟩ := card_eq_one.mp hzcard
  have hzmem : z ∈ a.filter (G.Adj (p.vertices 3)) := hz.symm ▸ mem_singleton_self z
  obtain ⟨hza, hcz⟩ := mem_filter.mp hzmem
  have hxz : ¬G.Adj p.leaf z := fun he ↦ h.no_common_column hcard hn z hza ⟨he, hcz⟩
  have hex : ∃ v ∈ a, G.Adj p.center v ∧ G.Adj p.leaf v := by
    by_contra hnone
    have hno : ∀ v ∈ a, ¬(G.Adj p.center v ∧ G.Adj p.leaf v) :=
      fun v hv he ↦ hnone ⟨v, hv, he⟩
    have hb := degree_pair_le_card p.center p.leaf a hno
    rw [h.leaf_three, h.core_complete.card_eq] at hb
    omega
  obtain ⟨v, hva, hrv, hxv⟩ := hex
  let ns := a.filter (G.Adj p.leaf)
  have hns3 : ns.card = 3 := h.leaf_three
  have hvns : v ∈ ns := mem_filter.mpr ⟨hva, hxv⟩
  have hrest : (ns.erase v).card = 2 := by rw [card_erase_of_mem hvns, hns3]
  obtain ⟨s, t, hst, hset⟩ := card_eq_two.mp hrest
  have hsns : s ∈ ns := (mem_erase.mp (by rw [hset]; simp : s ∈ ns.erase v)).2
  have htns : t ∈ ns := (mem_erase.mp (by rw [hset]; simp : t ∈ ns.erase v)).2
  obtain ⟨hsa, hxs⟩ := mem_filter.mp hsns
  obtain ⟨hta, hxt⟩ := mem_filter.mp htns
  have hsub : ns ⊆ a.erase z := by
    intro x hx
    obtain ⟨hxa, hxx⟩ := mem_filter.mp hx
    exact mem_erase.mpr ⟨fun he ↦ hxz (he ▸ hxx), hxa⟩
  have hns : ns = a.erase z := eq_of_subset_of_card_le hsub (by
    rw [card_erase_of_mem hza, h.core_complete.card_eq, hns3])
  have ha : a = {z, v, s, t} := by
    calc
      a = insert z (a.erase z) := (insert_erase hza).symm
      _ = insert z ns := by rw [hns]
      _ = insert z (insert v (ns.erase v)) := by rw [insert_erase hvns]
      _ = {z, v, s, t} := by rw [hset]
  exact ⟨z, v, s, t, ha, hza, hva, hsa, hta, hcz, hrv, hxv, hxs, hxt, hxz, hst⟩

end Erdos577.UniversalTriple

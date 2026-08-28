import ErdosProblems.Erdos577.JointFinalFullLeaf

/-! A three-contact old leaf forces a prohibited insertion in the prescribed triple. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma disjoint_rows_cover (z w : V) (j : Finset V)
    (hdis : ∀ u ∈ j, ¬(G.Adj z u ∧ G.Adj w u))
    (hsum : degreeIn G z j + degreeIn G w j = j.card) :
    ∀ u ∈ j, G.Adj z u ∨ G.Adj w u := by
  classical
  have he : j.filter (G.Adj z) ∪ j.filter (G.Adj w) = j := by
    apply eq_of_subset_of_card_le (union_subset (filter_subset _ _) (filter_subset _ _))
    rw [card_union_of_disjoint (neighbor_filters_disjoint z w j hdis)]
    exact hsum.ge
  intro u hu
  rw [← he] at hu
  rcases mem_union.mp hu with hu | hu
  · exact Or.inl (mem_filter.mp hu).2
  · exact Or.inr (mem_filter.mp hu).2

variable [Fintype V]

theorem Core.three_leaf_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hthree : degreeIn G p.leaf j = 3) : False := by
  have hy2 := h.last_degree_le_two hc hcard hn hj hjq hja hnine
  have hsum := hnine
  rw [h.arms_contacts] at hsum
  obtain ⟨_, hx1, hx2, _, _, h12⟩ := JointCore.four_distinct h.arms_card
  have hx : p.leaf ∈ spokes p d := by simp [spokes]
  have h1 : d 2 ∈ spokes p d := by simp [spokes]
  have h2 : d 3 ∈ spokes p d := by simp [spokes]
  have hcf := hc.presentPaw_feasible p h.config.1
  have hxrep : ∀ u ∈ j, QuadOn G (insert p.leaf (j.erase u)) := fun _ hu ↦
    hcf.terminal_universal_replace hj (by change 3 ≤ degreeIn G p.leaf j; omega) hu
  have hdis := no_common_of_universal_insertion (d 2) (d 3) p.leaf j
    (h.no_leaf_common hcard hn hj hja h1 h2 hx h12 hx1.symm hx2.symm) hxrep
  have hpair := degree_pair_le_card (d 2) (d 3) j hdis
  have hjcard := (c.property.blocks_quad j hj).card
  have hpairEq : degreeIn G (d 2) j + degreeIn G (d 3) j = j.card := by omega
  have hcover := disjoint_rows_cover (d 2) (d 3) j hdis hpairEq
  have hyexact : degreeIn G (q 3) j = 2 := by omega
  obtain ⟨jq, hjq'⟩ := c.property.blocks_quad j hj
  obtain ⟨v, hv, hrow⟩ := jq.exists_three_contact_labels p.leaf (by rwa [hjq'])
  have hvj : v.support = j := hv.trans hjq'
  have hv3 : v 3 ∈ j := hvj ▸ (v.mem_support _).mpr ⟨3, rfl⟩
  have hmiss : ¬G.Adj p.leaf (v 3) := fun he ↦ (hrow 3).mp he rfl
  have hafter : degreeIn G p.leaf (j.erase (v 3)) = 3 := by
    have he := degreeIn_erase_add G p.leaf (v 3) hv3
    rw [if_neg hmiss] at he
    omega
  have hdiag : G.Adj (v 1) (v 3) :=
    (hcf.terminal_replacement_diagonal hj v hvj 3 hafter).symm
  have hyout : q 3 ∉ v.support := by
    rw [hvj]
    exact fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint h.config.2.1 hj hjq.symm)
      ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  obtain ⟨i, hi, hrep⟩ := FullRow.replacement_in_first_three v (q 3) hyout hdiag
    (by rw [hvj, hyexact])
  rw [hvj] at hrep
  have hvi : v i ∈ j := hvj ▸ (v.mem_support _).mpr ⟨i, rfl⟩
  have hxi := (hrow i).mpr hi
  rcases hcover (v i) hvi with hzi | hzi
  · exact h.no_exposed_common hc hcard hn hj hjq hja hx h1 hx1 ⟨v i, hvi, hxi, hzi, hrep⟩
  · exact h.no_exposed_common hc hcard hn hj hjq hja hx h2 hx2 ⟨v i, hvi, hxi, hzi, hrep⟩

theorem Core.leaf_degree_le_two {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) : degreeIn G p.leaf j ≤ 2 := by
  have hbound := degreeIn_le_card G p.leaf j
  rw [(c.property.blocks_quad j hj).card] at hbound
  have hfour : degreeIn G p.leaf j ≠ 4 :=
    fun he ↦ h.full_leaf_false hc hcard hdeg hn hj hjq hja hnine he
  have hthree : degreeIn G p.leaf j ≠ 3 :=
    fun he ↦ h.three_leaf_false hc hcard hn hj hjq hja hnine he
  omega

end Erdos577.JointFinal

import ErdosProblems.Erdos577.JointClaimFourReversed

/-! Universal local classification bounds the old block and forces a distinct second heavy block. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_nine_outside_three31 {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hbs3 : bs.card = 3)
    (s : Finset V) (hs : s.card = 4)
    (hinside : contacts G s (c.remainder ∪ bs.biUnion id) ≤ 31) :
    ∃ b ∈ c.blocks, b ∉ bs ∧ 9 ≤ contacts G s b := by
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨b, hb, hbn, hh⟩ := c.exists_heavy_outside_selected bs hbs s (2 * k) 8 hdeg (by
    rw [hs]
    omega)
  exact ⟨b, hb, hbn, Nat.succ_le_of_lt hh⟩

theorem Core.exists_second_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a) :
    ∃ b ∈ c.blocks, b ≠ q.support ∧ b ≠ a ∧ b ≠ j ∧ 9 ≤ contacts G (arms p q d) b := by
  have hJ : contacts G (arms p q d) j ≤ 9 := by
    by_cases hnine : 9 ≤ contacts G (arms p q d) j
    · exact (h.local_conclusion hc hcard hdeg hn hj hjq hja hnine).1.le
    · omega
  obtain ⟨hp, hq, ha, haq, _, _, _⟩ := h.config
  have hfour := h.inside_four
  have hearm : ({p.leaf, d 2, d 3, q 3} : Finset V) = arms p q d := by
    simp only [arms]
    rw [insert_comm (q 3) (d 2), pair_comm (q 3) (d 3)]
  rw [hearm] at hfour
  have hdis : Disjoint (p.support ∪ q.support ∪ a) j :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨h.paw_disjoint hj, c.property.blocks_disjoint hq hj hjq.symm⟩,
      c.property.blocks_disjoint ha hj hja.symm⟩
  have hinside : contacts G (arms p q d) (p.support ∪ q.support ∪ a ∪ j) ≤ 31 := by
    rw [contacts_union_right G _ hdis]
    omega
  have hsel : ({q.support, a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hq (insert_subset ha (singleton_subset_iff.mpr hj))
  have hthree : ({q.support, a, j} : Finset (Finset V)).card = 3 :=
    card_triple_eq_three_iff.mpr ⟨haq.symm, hjq.symm, hja.symm⟩
  have he : c.remainder ∪ ({q.support, a, j} : Finset (Finset V)).biUnion id =
      p.support ∪ q.support ∪ a ∪ j := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← hp, union_assoc]
  obtain ⟨b, hb, hbn, hh⟩ := exists_nine_outside_three31 hcard hdeg
    {q.support, a, j} hsel hthree (arms p q d) h.arms_card (he.symm ▸ hinside)
  simp only [mem_insert, mem_singleton, not_or] at hbn
  exact ⟨b, hb, hbn.1, hbn.2.1, hbn.2.2, hh⟩

end Erdos577.JointFinal

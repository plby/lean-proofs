import ErdosProblems.Erdos577.WeightedTwelveSwap

/-! Five distinct rows have inside sum nineteen and force an eleven-contact outside block. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def five (p : Paw G) (q : Quadrilateral G) : Finset V := insert (q 3) p.support

lemma five_data (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support) :
    (five p q).card = 5 ∧ ∀ s : Finset V,
      contacts G (five p q) s = contacts G p.support s + degreeIn G (q 3) s := by
  have hy : q 3 ∉ p.support := fun hh ↦ disjoint_left.mp hd hh
    ((q.mem_support _).mpr ⟨3, rfl⟩)
  refine ⟨?_, ?_⟩
  · rw [five, card_insert_of_notMem hy, p.card_support]
  · intro s
    rw [five, contacts, sum_insert hy]
    change degreeIn G (q 3) s + contacts G p.support s = _
    omega

omit [DecidableRel G.Adj] in
lemma five_swap_eq (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) :
    five (exposedPaw p q hd h) (exposedQuad p q hd h) = five p q := by
  simp only [five, exposedQuad_apply, exposedPaw_support, p.support_eq]
  exact insert_comm _ _ _

variable [Fintype V]

theorem inside_nineteen {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q) :
    contacts G (five p q) (p.support ∪ q.support) = 19 := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  obtain ⟨hx, hb, ht⟩ := counts p q h
  have hr := center_zero hc hcard hn p hp hs q hq h
  have hT := p.contacts_triangle q.support
  change contacts G p.triangle q.support = degreeIn G p.center q.support +
    (degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support) at hT
  have hFQ : contacts G p.support q.support = 7 := by
    rw [p.contacts_support, hx, hT, hr, hb, ht]
  have hFF : contacts G p.support p.support = 8 := by
    rw [contacts_self_eq_twice_edgeCount G,
      p.edgeCount_of_no_quad (by rw [hp]; exact c.no_quad_remainder hcard hn)]
  have hym : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hyT : degreeIn G (q 3) p.triangle = 1 := by
    have hle := JointClaims.triangle_column_le_one hc hcard hn p hp hs
      (by rw [← hq, hx]) (q 3) (hq ▸ hym)
    have hpos : 0 < degreeIn G (q 3) p.triangle := card_pos.mpr
      ⟨p.vertices 3, mem_filter.mpr ⟨by simp [Paw.triangle], (first_rows p q h).2.symm⟩⟩
    omega
  have hyX : ¬G.Adj (q 3) p.leaf := fun hh ↦
    (by decide : ¬(7 : ℕ).testBit 3 = true) ((h.2.1 3).mp hh.symm)
  have hyF : degreeIn G (q 3) p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G (q 3) p.leaf p.leaf_not_mem_triangle,
      if_neg hyX, zero_add, hyT]
  have hyQ : degreeIn G (q 3) q.support = 3 := by
    rw [q.degreeIn_eq]
    change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 3
    rw [if_pos h.1.symm]
  rw [(five_data p q hd).2, contacts_union_right G _ hd, degreeIn_union G _ hd,
    hFF, hFQ, hyF, hyQ]

theorem exists_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q) :
    ∃ a ∈ c.blocks, a ≠ s ∧ 11 ≤ contacts G (five p q) a := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  apply c.exists_eleven_contact_outside_core hcard hdeg hs (five p q) (five_data p q hd).1
  rw [← hp, ← hq, inside_nineteen hc hcard hn p hp hs q hq h]

end Erdos577.WeightedTwelve

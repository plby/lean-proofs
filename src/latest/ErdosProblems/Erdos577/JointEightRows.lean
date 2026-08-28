import ErdosProblems.Erdos577.ClaimTwoThree

/-! Claim2.3 removes the CaseII center row and supplies the two extra inside bounds. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma center_internal_degree (p : Paw G) : degreeIn G p.center p.support = 3 := by
  have hT := degreeIn_clique G p.triangle_clique.isClique p.center_mem_triangle
  have hx : G.Adj p.center p.leaf := p.pendant.symm
  rw [p.triangle_clique.card_eq] at hT
  rw [p.support_eq, degreeIn_insert G p.center p.leaf p.leaf_not_mem_triangle,
    if_pos hx, hT]

variable [Fintype V]

theorem case_two_center_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hcase : CaseTwo p q) : degreeIn G p.center q.support = 0 := by
  have hseven := hcase.1
  have hx := degreeIn_le_card G p.leaf q.support
  have hb := degreeIn_le_card G (p.vertices 2) q.support
  rw [q.card_support] at hx hb
  by_cases hfull : degreeIn G p.leaf q.support = 4
  · by_contra hh
    have hpos : 0 < degreeIn G p.center s := hq ▸ Nat.pos_of_ne_zero hh
    have hbound := (hc.claim_two_three hcard hdeg hn p hp hs (hq ▸ hfull) hpos).1
    rw [← hq] at hbound
    omega
  · have hthree : degreeIn G p.leaf q.support = 3 := by omega
    have hbfull : degreeIn G (p.vertices 2) q.support = 4 := by omega
    have hbound := triangle_contacts_le_four hc hcard hn p hp hs (by rw [← hq, hthree])
    rw [← hq] at hbound
    have he := p.contacts_triangle q.support
    change contacts G p.triangle q.support = degreeIn G p.center q.support +
      (degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support) at he
    omega

theorem case_two_center_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hcase : CaseTwo p q) : degreeIn G p.center (p.support ∪ q.support) = 3 := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  rw [degreeIn_union G p.center hd, center_internal_degree,
    case_two_center_zero hc hcard hdeg hn p hp hs q hq hcase, add_zero]

theorem last_inside_le_five {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hcase : CaseOne p q ∨ CaseTwo p q) : degreeIn G (q 3) (p.support ∪ q.support) ≤ 5 := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hm : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hT := triangle_column_le_one hc hcard hn p hp hs (hq ▸ leaf_lower p q hcase)
    (q 3) (hq ▸ hm)
  have hF : degreeIn G (q 3) p.support ≤ 2 := by
    rw [p.support_eq, degreeIn_insert G (q 3) p.leaf p.leaf_not_mem_triangle]
    split_ifs <;> omega
  have hQ := degreeIn_le_card G (q 3) (q.support.erase (q 3))
  rw [degreeIn_erase_self G (q 3) hm, card_erase_of_mem hm, q.card_support] at hQ
  rw [degreeIn_union G (q 3) hd]
  omega

end Erdos577.JointClaims

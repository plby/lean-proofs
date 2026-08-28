import ErdosProblems.Erdos577.CoreObstructionRoutes
import ErdosProblems.Erdos577.PawEdgeCount

/-! Exact inside identities and paw-contact bounds for the seven-vertex core obstruction. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Strong.remainder_self_contacts {c : TriangleChain G} (hc : c.Strong)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    contacts G c.remainder c.remainder = 8 := by
  obtain ⟨p, _, _, hp⟩ := hc.exists_paw
  have he := p.edgeCount_of_no_quad (by rw [hp]; exact c.no_quad_remainder hcard hn)
  rw [hp] at he
  rw [contacts_self_eq_twice_edgeCount, he]

theorem TriangleChain.Strong.block_contacts_le_twelve {c : TriangleChain G} (hc : c.Strong)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) {b : Finset V} (hb : b ∈ c.blocks) :
    contacts G c.remainder b ≤ 12 := by
  obtain ⟨p, _, _, hp⟩ := hc.exists_paw
  obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
  have hh := hc.toFeasible.paw_contacts_le_twelve hcard hdeg hn p hp hb q hq
  rwa [hp, hq] at hh

theorem TriangleChain.Strong.block_contacts_le_eight_of_terminal_two {c : TriangleChain G}
    (hc : c.Strong) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hrow : 2 ≤ degreeIn G c.terminal b) :
    contacts G c.remainder b ≤ 8 := by
  obtain ⟨p, hx, _, hp⟩ := hc.exists_paw
  obtain ⟨q, hq⟩ := c.property.blocks_quad b hb
  have hh := hc.toFeasible.two_leaf_contacts_le_eight hcard hdeg hn p hp hb q hq
    (by rw [hx, hq]; exact hrow)
  rwa [hp, hq] at hh

namespace CoreTransfer

omit [Fintype V] in
lemma low_pair_contacts_cycle (q : Quadrilateral G) (hn : ¬G.Adj (q 1) (q 3)) :
    contacts G {q 1, q 3} q.support = 4 := by
  have hne : q 1 ≠ q 3 := q.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  rw [contacts, sum_pair hne, q.degreeIn_eq, q.degreeIn_eq]
  change (2 + if G.Adj (q 1) (q 3) then 1 else 0) +
    (2 + if G.Adj (q 3) (q 1) then 1 else 0) = 4
  rw [if_neg hn, if_neg (fun hh ↦ hn hh.symm)]

lemma low_contacts_remainder_block (c : TriangleChain G) (q : Quadrilateral G)
    {b : Finset V} (hb : b ∈ c.blocks) :
    contacts G {q 1, q 3} (c.remainder ∪ b) = degreeIn G c.terminal {q 1, q 3} +
      degreeIn G (q 1) (c.triangle ∪ b) + degreeIn G (q 3) (c.triangle ∪ b) := by
  have hx : c.terminal ∉ c.triangle ∪ b := by
    intro hh
    exact (mem_union.mp hh).elim c.property.terminal_not_mem (c.terminal_not_mem_block hb)
  have he : c.remainder ∪ b = {c.terminal} ∪ (c.triangle ∪ b) := by
    change insert c.terminal c.triangle ∪ b = _
    rw [singleton_union, insert_union]
  have hne : q 1 ≠ q 3 := q.injective.ne (by decide : (1 : Fin 4) ≠ 3)
  rw [he, contacts_union_right G _ (disjoint_singleton_left.mpr hx), contacts_singleton_right]
  rw [contacts, sum_pair hne]
  omega

lemma rows_inside_two_blocks (c : TriangleChain G) (q : Quadrilateral G)
    (hq : q.support ∈ c.blocks) {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hn : ¬G.Adj (q 1) (q 3)) :
    contacts G (rows c q) (c.remainder ∪ (b ∪ q.support)) =
      contacts G c.remainder c.remainder + contacts G c.remainder b +
        contacts G c.remainder q.support + contacts G {q 1, q 3} (c.remainder ∪ b) + 4 := by
  have hdb : Disjoint c.remainder b := by
    apply disjoint_left.mpr
    intro u hu hub
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hub)).2 hu
  have hdq : Disjoint c.remainder q.support := by
    apply disjoint_left.mpr
    intro u hu huq
    exact (mem_sdiff.mp (c.complementPartition.block_subset hq huq)).2 hu
  have hdc : Disjoint (c.remainder ∪ b) q.support :=
    disjoint_union_left.mpr ⟨hdq, c.property.blocks_disjoint hb hq hbq⟩
  have he : c.remainder ∪ (b ∪ q.support) = (c.remainder ∪ b) ∪ q.support :=
    (union_assoc _ _ _).symm
  rw [rows, contacts_union_left G (remainder_disjoint_lows c q hq), he,
    contacts_union_right G c.remainder hdc, contacts_union_right G c.remainder hdb,
    contacts_union_right G {q 1, q 3} hdc, low_pair_contacts_cycle q hn]
  omega

omit [Fintype V] in
lemma terminal_low_degree_le_one (q : Quadrilateral G) (x : V)
    (h0 : G.Adj x (q 0)) (hrow : degreeIn G x q.support ≤ 2) :
    degreeIn G x {q 1, q 3} ≤ 1 := by
  have hs : ({q 0, q 1, q 3} : Finset V) ⊆ q.support := by
    intro u hu
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with hu | hu | hu
    · exact hu ▸ (q.mem_support _).mpr ⟨0, rfl⟩
    · exact hu ▸ (q.mem_support _).mpr ⟨1, rfl⟩
    · exact hu ▸ (q.mem_support _).mpr ⟨3, rfl⟩
  have hnot : q 0 ∉ ({q 1, q 3} : Finset V) := by
    simp only [mem_insert, mem_singleton, not_or]
    exact ⟨q.injective.ne (by decide), q.injective.ne (by decide)⟩
  have hm := degreeIn_mono G x hs
  rw [degreeIn_insert G x (q 0) hnot, if_pos h0] at hm
  omega

omit [Fintype V] in
lemma terminal_low_degree_zero (q : Quadrilateral G) (x : V)
    (hrow : ∀ j : Fin 4, G.Adj x (q j) ↔ (5 : ℕ).testBit j.val = true) :
    degreeIn G x {q 1, q 3} = 0 := by
  have h1 : ¬G.Adj x (q 1) := fun hh ↦ by have hh' := (hrow 1).mp hh; contradiction
  have h3 : ¬G.Adj x (q 3) := fun hh ↦ by have hh' := (hrow 3).mp hh; contradiction
  simp [degreeIn, h1, h3]

end CoreTransfer

end Erdos577

import ErdosProblems.Erdos577.JointSetupSwap
import ErdosProblems.Erdos577.PawEdgeCount
import ErdosProblems.Erdos577.OutsideCoreCount

/-! The six weighted slots have inside sum at most23 and force an outside weight at least13. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The third triangle vertex is deliberately counted twice. -/
def sixWeight (p : Paw G) (q : Quadrilateral G) (a : Finset V) : ℕ :=
  contacts G p.support a + degreeIn G (p.vertices 3) a + degreeIn G (q 3) a

lemma sixWeight_eq_rows (p : Paw G) (q : Quadrilateral G) (a : Finset V) :
    sixWeight p q a = degreeIn G p.leaf a + degreeIn G (q 3) a + degreeIn G p.center a +
      degreeIn G (p.vertices 2) a + 2 * degreeIn G (p.vertices 3) a := by
  rw [sixWeight, p.contacts_support, p.contacts_triangle]
  change _ = degreeIn G p.leaf a + degreeIn G (q 3) a + degreeIn G (p.vertices 1) a +
    degreeIn G (p.vertices 2) a + 2 * degreeIn G (p.vertices 3) a
  omega

lemma third_internal_degree (p : Paw G) (hn : ¬QuadOn G p.support) :
    degreeIn G (p.vertices 3) p.support = 2 := by
  have hT := degreeIn_clique G p.triangle_clique.isClique
    (show p.vertices 3 ∈ p.triangle by simp [Paw.triangle])
  rw [p.triangle_clique.card_eq] at hT
  have hx : ¬G.Adj (p.vertices 3) p.leaf := fun hh ↦ (p.nonadjacent_of_no_quad hn).2 hh.symm
  rw [p.support_eq, degreeIn_insert G (p.vertices 3) p.leaf p.leaf_not_mem_triangle,
    if_neg hx, zero_add, hT]

variable [Fintype V]

theorem inside_upper {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (h : CaseOne p q ∨ CaseTwo p q) : sixWeight p q (p.support ∪ q.support) ≤ 23 := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hpno : ¬QuadOn G p.support := by rw [hp]; exact c.no_quad_remainder hcard hn
  have hFF : contacts G p.support p.support = 8 := by
    rw [contacts_self_eq_twice_edgeCount G, p.edgeCount_of_no_quad hpno]
  have hcF := third_internal_degree p hpno
  have hcQ := third_row_zero hc hcard hn p hp hs q hq h
  have hthree : 3 ≤ degreeIn G p.leaf s := hq ▸ leaf_lower p q h
  have hTQ := triangle_contacts_le_four hc hcard hn p hp hs hthree
  rw [← hq] at hTQ
  have hxQ := degreeIn_le_card G p.leaf q.support
  rw [q.card_support] at hxQ
  have hFQ : contacts G p.support q.support ≤ 8 := by
    rw [p.contacts_support]
    omega
  have hlastT := triangle_column_le_one hc hcard hn p hp hs hthree (q 3)
    (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩)
  have hlastF : degreeIn G (q 3) p.support ≤ 2 := by
    rw [p.support_eq, degreeIn_insert G (q 3) p.leaf p.leaf_not_mem_triangle]
    split_ifs <;> omega
  have hlastQ : degreeIn G (q 3) q.support ≤ 3 := by
    have hh := degreeIn_le_card G (q 3) (q.support.erase (q 3))
    have hm := (q.mem_support _).mpr ⟨3, rfl⟩
    rw [degreeIn_erase_self G (q 3) hm, card_erase_of_mem hm, q.card_support] at hh
    exact hh
  rw [sixWeight, contacts_union_right G p.support hd,
    degreeIn_union G (p.vertices 3) hd, degreeIn_union G (q 3) hd]
  omega

theorem exists_heavy_of_inside {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hinside : sixWeight p q (p.support ∪ q.support) ≤ 23) :
    ∃ a ∈ c.blocks, a ≠ s ∧ 13 ≤ sixWeight p q a := by
  have htotalF := minimum_degree_sum G p.support (2 * k) (fun u _ ↦ hdeg u)
  rw [p.card_support] at htotalF
  have htotalC := hdeg (p.vertices 3)
  have htotalQ := hdeg (q 3)
  have hidF := c.contacts_core_add_outside hs p.support
  have hidC := c.contacts_core_add_outside hs {p.vertices 3}
  have hidQ := c.contacts_core_add_outside hs {q 3}
  simp only [contacts_singleton_left, degreeIn_univ] at hidC hidQ
  have hcore : c.remainder ∪ s = p.support ∪ q.support := by rw [hp, hq]
  rw [hcore] at hidF hidC hidQ
  have hblocks := c.card_vertices
  have herase := card_erase_of_mem hs
  have hpos : 0 < c.blocks.card := card_pos.mpr ⟨s, hs⟩
  by_contra! hn
  have hbound : (∑ a ∈ c.blocks.erase s, sixWeight p q a) ≤ (c.blocks.erase s).card * 12 := by
    calc
      _ ≤ ∑ _ ∈ c.blocks.erase s, 12 := sum_le_sum fun a ha ↦ by
        have hh := hn a (mem_erase.mp ha).2 (mem_erase.mp ha).1
        omega
      _ = _ := by simp
  simp only [sixWeight, sum_add_distrib] at hbound
  unfold sixWeight at hinside
  omega

theorem exists_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (h : CaseOne p q ∨ CaseTwo p q) : ∃ a ∈ c.blocks, a ≠ s ∧ 13 ≤ sixWeight p q a :=
  exists_heavy_of_inside hcard hdeg p hp hs q hq (inside_upper hc hcard hn p hp hs q hq h)

end Erdos577.JointClaims

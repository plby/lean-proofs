import ErdosProblems.Erdos577.WeightedFourteenLowTerminals
import ErdosProblems.Erdos577.FirstPawLeafCount

/-! Exact row sizes and both nine-contact paw bounds at the heavy block for pattern (14). -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a) :
    degreeIn G p.leaf a = 2 ∧ degreeIn G (q 1) a = 2 ∧
      1 ≤ degreeIn G (q 3) a ∧ degreeIn G (q 3) a ≤ 2 ∧
      9 ≤ contacts G p.support a ∧ 9 ≤ degreeIn G (q 3) a + contacts G p.triangle a ∧
      (contacts G p.support a = 9 → degreeIn G (q 3) a = 2) := by
  obtain ⟨hxpos, hwpos, hE, hE'⟩ := positive_leaves_and_heavy_paws hc hcard hn p hp hb q hq
    hd h ha hab hheavy
  have hlow := terminal_degree_le_two hc hcard hn p hp hb q hq hd h ha hab hheavy
  have hxmax := hlow 0
  have hymax := hlow 1
  have hwmax := hlow 2
  change degreeIn G p.leaf a ≤ 2 at hxmax
  change degreeIn G (q 1) a ≤ 2 at hymax
  change degreeIn G (q 3) a ≤ 2 at hwmax
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  have hclass := hc.first_paw_classification hcard hdeg hn p hp ha v hv
    (by rw [hv]; exact hE) (by rw [hv]; exact hxpos)
  have hEmax := hclass.1
  rw [hv] at hEmax
  have hsum := p.contacts_support a
  change 17 ≤ 2 * degreeIn G p.leaf a + 2 * degreeIn G (q 1) a + degreeIn G (q 3) a +
    contacts G p.triangle a at hheavy
  have hx2 : degreeIn G p.leaf a = 2 := by
    by_contra hh
    have hx1 : degreeIn G p.leaf v.support = 1 := by rw [hv]; omega
    have h9 := hclass.one_leaf_bound p v hx1
    rw [hv] at h9
    omega
  exact ⟨hx2, by omega, hwpos, hwmax, hE, hE', fun hh ↦ by omega⟩

theorem exists_heavy_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 17 ≤ weight p q a ∧
      degreeIn G p.leaf a = 2 ∧ degreeIn G (q 1) a = 2 ∧
      1 ≤ degreeIn G (q 3) a ∧ degreeIn G (q 3) a ≤ 2 ∧
      9 ≤ contacts G p.support a ∧ 9 ≤ degreeIn G (q 3) a + contacts G p.triangle a ∧
      (contacts G p.support a = 9 → degreeIn G (q 3) a = 2) := by
  obtain ⟨a, ha, hab, hh⟩ := heavy_block hcard hdeg hn p hp hb q hq hd h
  exact ⟨a, ha, hab, hh, heavy_rows hc hcard hdeg hn p hp hb q hq hd h ha hab hh⟩

end Erdos577.WeightedFourteen

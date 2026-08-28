import ErdosProblems.Erdos577.WeightedFourteenHighRows
import ErdosProblems.Erdos577.WeightedFourteenFullGain
import ErdosProblems.Erdos577.DenseOutside

/-! The three terminal rows are small; both paws have positive leaves and heavy contact totals. -/

namespace Erdos577.WeightedFourteen

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem terminal_degree_le_two {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a)
    (tag : Fin 3) : degreeIn G (terminal p q tag) a ≤ 2 := by
  by_contra! hh
  obtain ⟨hcl, hx, hy, _, hr⟩ := high_rows_full hc hcard hn p hp hb q hq hd h ha hab hheavy
    ⟨tag, hh⟩
  exact no_full_principal_rows hc p hp hb q hq hd h ha hab hcl hx hy hr

theorem terminal_degree_le_one_of_dense {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hT : 9 ≤ contacts G p.triangle a) (tag : Fin 3) : degreeIn G (terminal p q tag) a ≤ 1 := by
  obtain ⟨d, hdF, hdx, hdt, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h tag
  have hh := hdF.terminal_degree_le_one_of_dense hcard hn (hkeep a ha hab) (by rw [hdt]; exact hT)
  rwa [hdx] at hh

theorem positive_leaves_and_heavy_paws {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a) :
    0 < degreeIn G p.leaf a ∧ 0 < degreeIn G (q 3) a ∧
      9 ≤ contacts G p.support a ∧ 9 ≤ degreeIn G (q 3) a + contacts G p.triangle a := by
  have hlow := terminal_degree_le_two hc hcard hn p hp hb q hq hd h ha hab hheavy
  have hx2 := hlow 0
  have hy2 := hlow 1
  have hw2 := hlow 2
  change degreeIn G p.leaf a ≤ 2 at hx2
  change degreeIn G (q 1) a ≤ 2 at hy2
  change degreeIn G (q 3) a ≤ 2 at hw2
  change 17 ≤ 2 * degreeIn G p.leaf a + 2 * degreeIn G (q 1) a + degreeIn G (q 3) a +
    contacts G p.triangle a at hheavy
  have hTmax := contacts_le_card_mul G p.triangle a
  rw [p.triangle_clique.card_eq, (c.property.blocks_quad a ha).card] at hTmax
  have hdense := terminal_degree_le_one_of_dense hc hcard hn p hp hb q hq hd h ha hab
  have hxpos : 0 < degreeIn G p.leaf a := by
    by_contra! hh
    have hy := hdense (by omega) 1
    have hw := hdense (by omega) 2
    change degreeIn G (q 1) a ≤ 1 at hy
    change degreeIn G (q 3) a ≤ 1 at hw
    omega
  have hwpos : 0 < degreeIn G (q 3) a := by
    by_contra! hh
    have hx := hdense (by omega) 0
    have hy := hdense (by omega) 1
    change degreeIn G p.leaf a ≤ 1 at hx
    change degreeIn G (q 1) a ≤ 1 at hy
    omega
  have he : contacts G p.support a = degreeIn G p.leaf a + contacts G p.triangle a := by
    rw [p.support_eq, contacts, sum_insert p.leaf_not_mem_triangle]
    rfl
  exact ⟨hxpos, hwpos, by omega, by omega⟩

end Erdos577.WeightedFourteen

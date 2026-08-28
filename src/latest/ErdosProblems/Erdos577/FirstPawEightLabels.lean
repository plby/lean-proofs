import ErdosProblems.Erdos577.FirstPawEightRows
import ErdosProblems.Erdos577.ThreeContactLabels

/-! Normalize the heavier original low row and the outside block's exact three-contact labeling. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
lemma PawBlock.Pattern8.reverse (p : Paw G) (q : Quadrilateral G) (h : PawBlock.Pattern8 p q) :
    PawBlock.Pattern8 p q.reverse := by
  refine ⟨h.1, ?_⟩
  intro i j
  have hbits : ∀ i j : Fin 4,
      ((![1, 15, 15, 0] : Fin 4 → ℕ) i).testBit (-j).val =
        ((![1, 15, 15, 0] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
  change G.Adj (p.vertices i) (q (-j)) ↔ _
  rw [h.2 i (-j), hbits i j]

namespace FirstPawEight

lemma reverse_rows (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (hd' : Disjoint p.support q.reverse.support) : rows p q.reverse hd' = rows p q hd := by
  rw [rows_eq, rows_eq]
  change ({p.leaf, p.vertices 3, q 3, q 1} : Finset V) = {p.leaf, p.vertices 3, q 1, q 3}
  rw [pair_comm (q 3) (q 1)]

variable [Fintype V] [DecidableRel G.Adj]

theorem low_row_bounds {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a) :
    degreeIn G p.leaf a ≤ 2 ∧ degreeIn G (p.vertices 3) a ≤ 2 ∧
      degreeIn G (q 1) a ≤ 3 ∧ degreeIn G (q 3) a ≤ 3 ∧
      5 ≤ degreeIn G (q 1) a + degreeIn G (q 3) a := by
  have hx : degreeIn G p.leaf a ≤ 2 :=
    terminal_bound hc hcard hn p hp hb q hq hd h ha hab hheavy false
  have hc3 : degreeIn G (p.vertices 3) a ≤ 2 :=
    terminal_bound hc hcard hn p hp hb q hq hd h ha hab hheavy true
  have h1 : degreeIn G (q 1) a ≤ 3 := row_bound hcard hn p hp hb q hq hd h ha hab hheavy 5
    (by decide +kernel)
  have h3 : degreeIn G (q 3) a ≤ 3 := row_bound hcard hn p hp hb q hq hd h ha hab hheavy 7
    (by decide +kernel)
  have hid := rows_contacts p q hd a
  exact ⟨hx, hc3, h1, h3, by omega⟩

theorem exists_first_low_three {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a) :
    ∃ q' : Quadrilateral G, q'.support = q.support ∧ PawBlock.Pattern8 p q' ∧
      degreeIn G (q' 1) a = 3 ∧
      ∃ hd' : Disjoint p.support q'.support, rows p q' hd' = rows p q hd := by
  obtain ⟨_, _, h1, h3, hsum⟩ := low_row_bounds hc hcard hn p hp hb q hq hd h ha hab hheavy
  by_cases he : degreeIn G (q 1) a = 3
  · exact ⟨q, rfl, h, he, hd, rfl⟩
  · have he3 : degreeIn G (q 3) a = 3 := by omega
    have hd' : Disjoint p.support q.reverse.support := by rw [q.reverse_support]; exact hd
    exact ⟨q.reverse, q.reverse_support, h.reverse p q, he3, hd', reverse_rows p q hd hd'⟩

theorem exists_outside_labels {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern8 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 9 ≤ contacts G (rows p q hd) a)
    (hthree : 3 ≤ degreeIn G (q 1) a) :
    ∃ d : Quadrilateral G, d.support = a ∧
      (∀ j : Fin 4, G.Adj (q 1) (d j) ↔ j ≠ 3) ∧ ¬G.Adj (d 1) (d 3) := by
  obtain ⟨d, hdA⟩ := c.property.blocks_quad a ha
  have hout : q 1 ∉ a := fun hh ↦
    disjoint_left.mp (c.property.blocks_disjoint hb ha hab.symm)
      (hq ▸ (q.mem_support _).mpr ⟨1, rfl⟩) hh
  have hnu : ¬∀ u ∈ a, QuadOn G (insert (q 1) (a.erase u)) :=
    no_universal hcard hn p hp hb q hq hd h ha hab hheavy 5 (by decide +kernel)
  obtain ⟨_, v, hv, hrow, hdiag⟩ := d.exists_nonuniversal_three_labels (q 1)
    (by rw [hdA]; exact hout) (by rw [hdA]; exact hthree) (by rw [hdA]; exact hnu)
  exact ⟨v, hv.trans hdA, hrow, hdiag⟩

end FirstPawEight

end Erdos577

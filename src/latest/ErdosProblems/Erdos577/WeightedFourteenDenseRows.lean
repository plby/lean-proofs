import ErdosProblems.Erdos577.WeightedFourteenCenterTwo

/-! Three literal matrices record which triangle vertex has the unique extra contact. -/

namespace Erdos577.WeightedFourteen.Dense

def pawRows : Fin 3 → Fin 4 → ℕ := ![![5, 13, 5, 5], ![5, 5, 13, 5], ![5, 5, 5, 13]]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Rows (p : Paw G) (q v : Quadrilateral G) (special : Fin 3) : Prop :=
  PawBlock.OnlyFirst v ∧ PawBlock.ExactRows p v (pawRows special) ∧
    (∀ j : Fin 4, G.Adj (q 1) (v j) ↔ (5 : ℕ).testBit j.val = true) ∧
    (∀ j : Fin 4, G.Adj (q 3) (v j) ↔ (5 : ℕ).testBit j.val = true)

omit [DecidableEq V] in
lemma paw_rows_of_alternatives (p : Paw G) (v : Quadrilateral G)
    (h : PawBlock.ExactRows p v ![5, 13, 5, 5] ∨
      ∃ swap : Bool, PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) v ![5, 5, 13, 5]) :
    ∃ special : Fin 3, PawBlock.ExactRows p v (pawRows special) := by
  rcases h with h | ⟨swap, h⟩
  · exact ⟨0, h⟩
  · cases swap
    · exact ⟨1, h⟩
    · refine ⟨2, ?_⟩
      intro i j
      fin_cases i
      · exact h 0 j
      · exact h 1 j
      · exact h 3 j
      · exact h 2 j

omit [DecidableEq V] in
lemma Rows.leaf (p : Paw G) (q v : Quadrilateral G) (special : Fin 3)
    (h : Rows p q v special) :
    ∀ j : Fin 4, G.Adj p.leaf (v j) ↔ (5 : ℕ).testBit j.val = true := by
  intro j
  have hh := h.2.1 0 j
  fin_cases special <;> exact hh

omit [DecidableEq V] in
lemma Rows.paw_low_absent (p : Paw G) (q v : Quadrilateral G) (special : Fin 3)
    (h : Rows p q v special) (i : Fin 4) : ¬G.Adj (p.vertices i) (v 1) := by
  intro he
  have hb := (h.2.1 i 1).mp he
  have hbits : ∀ special : Fin 3, ∀ i : Fin 4, (pawRows special i).testBit 1 = false := by
    decide +kernel
  change (pawRows special i).testBit 1 = true at hb
  rw [hbits] at hb
  contradiction

variable [Fintype V] [DecidableRel G.Adj]

theorem rows_at_heavy {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a) :
    ∃ v : Quadrilateral G, ∃ special : Fin 3, v.support = a ∧ Rows p q v special := by
  obtain ⟨_, v, hv, hdiag, hrows, hy, hw⟩ := joint_rows_at_heavy hc hcard hdeg hn
    p hp hb q hq hd h ha hab hheavy
  obtain ⟨special, hs⟩ := paw_rows_of_alternatives p v hrows
  exact ⟨v, special, hv, hdiag, hs, hy, hw⟩

end Erdos577.WeightedFourteen.Dense

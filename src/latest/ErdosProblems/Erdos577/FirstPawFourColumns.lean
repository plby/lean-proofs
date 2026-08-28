import ErdosProblems.Erdos577.FirstPawSixColumns
import ErdosProblems.Erdos577.FirstPawRowBounds
import ErdosProblems.Erdos577.CycleLabels

/-! The high-pair leaf and a complete triangle column in the first paw's case (4). -/

namespace Erdos577.PawBlock

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Pattern4.leaf_exact (p : Paw G) (q : Quadrilateral G) (h : Pattern4 p q)
    (hleaf : degreeIn G p.leaf q.support = 2) : WeightedPawBlock.Row p q 0 5 := by
  apply q.row_saturated (p.vertices 0) 5
  · intro j hj
    rcases h.2.2.2 j (Or.inl hj) with rfl | rfl <;> decide
  · change _ ≤ degreeIn G p.leaf q.support
    rw [hleaf]
    decide +kernel

lemma Pattern4.full_high_column (p : Paw G) (q : Quadrilateral G) (h : Pattern4 p q)
    (hleaf : degreeIn G p.leaf q.support = 2) (hheavy : 9 ≤ contacts G p.support q.support) :
    degreeIn G (q 0) p.triangle = 3 ∨ degreeIn G (q 2) p.triangle = 3 := by
  have hlow (j : Fin 4) (hj : j = 1 ∨ j = 3) : degreeIn G (q j) p.triangle ≤ 1 := by
    have hidx : j ≠ 0 ∧ j ≠ 2 := by rcases hj with rfl | rfl <;> decide
    have hb : ¬G.Adj (p.vertices 2) (q j) := by
      intro he
      rcases h.2.2.2 j (Or.inr (Or.inl he)) with hh | hh
      · exact hidx.1 hh
      · exact hidx.2 hh
    have hc : ¬G.Adj (p.vertices 3) (q j) := by
      intro he
      rcases h.2.2.2 j (Or.inr (Or.inr he)) with hh | hh
      · exact hidx.1 hh
      · exact hidx.2 hh
    have he := p.triangle_column (q j)
    rw [if_neg hb, if_neg hc] at he
    split_ifs at he <;> omega
  have h0 := degreeIn_le_card G (q 0) p.triangle
  have h2 := degreeIn_le_card G (q 2) p.triangle
  rw [p.triangle_clique.card_eq] at h0 h2
  have h1 := hlow 1 (Or.inl rfl)
  have h3 := hlow 3 (Or.inr rfl)
  have hcols := p.triangle_columns_sum q
  have htotal := p.contacts_support q.support
  omega

lemma Pattern4.rotate_two (p : Paw G) (q : Quadrilateral G) (h : Pattern4 p q) :
    Pattern4 p (q.rotate 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.1.symm
  · rw [q.rotate_support]
    exact h.2.1
  · rw [q.rotate_support]
    exact h.2.2.1
  · intro j hj
    have hh := h.2.2.2 (j + 2) hj
    have hidx : ∀ j : Fin 4, (j + 2 = 0 ∨ j + 2 = 2) → j = 0 ∨ j = 2 := by
      decide +kernel
    exact hidx j hh

lemma Pattern4.exists_full_first (p : Paw G) (q : Quadrilateral G) (h : Pattern4 p q)
    (hleaf : degreeIn G p.leaf q.support = 2) (hheavy : 9 ≤ contacts G p.support q.support) :
    ∃ v : Quadrilateral G, v.support = q.support ∧ Pattern4 p v ∧
      degreeIn G (v 0) p.triangle = 3 := by
  rcases h.full_high_column p q hleaf hheavy with h0 | h2
  · exact ⟨q, rfl, h, h0⟩
  · exact ⟨q.rotate 2, q.rotate_support 2, h.rotate_two p q, h2⟩

end Erdos577.PawBlock

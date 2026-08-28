import ErdosProblems.Erdos577.FullLeafSixLowRows

/-! A high first row supplies universal replacements, a diagonal, and four second contacts. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.first_last_diagonal (h : Configuration c p s a y)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    {x : V} (hx : x ∈ insert p.leaf s)
    (hrow : ∀ i : Fin 4, i ≠ 3 → G.Adj x (q i)) : G.Adj (q 1) (q 3) := by
  obtain ⟨e, he, hex, _, _, _, hkeep⟩ := h.exposed_chain hx
  have hthree := q.degree_after_erase_eq_three x 3 hrow
  have hd := he.terminal_replacement_diagonal (hkeep q.support hj hjs) q rfl 3
    (by rwa [hex])
  exact hd.symm

theorem Configuration.first_high_edges (h : Configuration c p s a y)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s)
    {x : V} (hx : x ∈ insert p.leaf s) (hrow : 3 ≤ degreeIn G x j) :
    5 ≤ edgeCount G j := by
  by_cases hfour : degreeIn G x j = 4
  · have hcl := h.complete_of_first_full hx hj hjs hfour
    rw [edgeCount_clique hcl.isClique, hcl.card_eq]
    decide
  · obtain ⟨q, hq⟩ := c.property.blocks_quad j hj
    have hbound : degreeIn G x j ≤ 4 :=
      (degreeIn_le_card G x j).trans_eq (c.property.blocks_quad j hj).card
    obtain ⟨v, hv, hlabels⟩ := q.exists_three_contact_labels x (by rw [hq]; omega)
    have hd := h.first_last_diagonal v (by rwa [hv, hq]) (by rwa [hv, hq]) hx
      (fun i hi ↦ (hlabels i).mpr hi)
    rw [← hq, ← hv, v.edgeCount_eq, if_pos hd]
    omega

theorem Configuration.high_first_matched_columns (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {x : V} (hx : x ∈ insert p.leaf s) (hrow : 3 ≤ degreeIn G x j) :
    ∀ v ∈ j, degreeIn G v (FullLeafEquality.matchedSecond p s a y) ≤ 1 := by
  intro v hv
  exact (degreeIn_mono G v h.matched_second_subset).trans
    (h.core_degree_of_first_replacement hcard hn hx hj hjs hja hv
      (h.first_universal_replacements hx hj hjs hrow v hv))

theorem Configuration.high_first_matched_contacts_le_four (h : Configuration c p s a y)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    {x : V} (hx : x ∈ insert p.leaf s) (hrow : 3 ≤ degreeIn G x j) :
    contacts G (FullLeafEquality.matchedSecond p s a y) j ≤ 4 := by
  rw [contacts_comm]
  calc
    contacts G j (FullLeafEquality.matchedSecond p s a y) ≤ ∑ _ ∈ j, (1 : ℕ) :=
      sum_le_sum (h.high_first_matched_columns hcard hn hj hjs hja hx hrow)
    _ = 4 := by rw [sum_const, smul_eq_mul, (c.property.blocks_quad j hj).card]

end Erdos577.FullLeafCore

import ErdosProblems.Erdos577.JointPairBounds

/-! Choose the heavier distinguished row and a first-three labeling, retaining full rows. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exists_three_included_labels (q : Quadrilateral G) (z : V)
    (hthree : 3 ≤ degreeIn G z q.support) :
    ∃ v : Quadrilateral G, v.support = q.support ∧
      ∀ i : Fin 4, i ≠ 3 → G.Adj z (v i) := by
  by_cases hfour : degreeIn G z q.support = 4
  · have hfull := (degreeIn_eq_card_iff (G := G) z q.support).mp (hfour.trans q.card_support.symm)
    exact ⟨q, rfl, fun i _ ↦ hfull (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)⟩
  · have hbound := degreeIn_le_card G z q.support
    rw [q.card_support] at hbound
    obtain ⟨v, hv, hrow⟩ := q.exists_three_contact_labels z (by omega)
    refine ⟨v, hv, ?_⟩
    intro i hi
    fin_cases i
    · exact (hrow 0).mpr (by decide)
    · exact (hrow 1).mpr (by decide)
    · exact (hrow 2).mpr (by decide)
    · exact False.elim (hi rfl)

variable [Fintype V]

theorem Core.exists_opposite_pair_labels {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j) :
    ∃ z w : V, ∃ v : Quadrilateral G,
      (z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2) ∧
      degreeIn G w j ≤ degreeIn G z j ∧ v.support = j ∧
      (∀ i : Fin 4, i ≠ 3 → G.Adj z (v i)) ∧
      degreeIn G p.leaf {v 0, v 2} ≤ 1 ∧ degreeIn G p.leaf {v 1, v 3} ≤ 1 ∧
      degreeIn G (q 3) {v 0, v 2} ≤ 1 ∧ degreeIn G (q 3) {v 1, v 3} ≤ 1 ∧
      degreeIn G w {v 1, v 3} ≤ 1 := by
  have hx := h.leaf_degree_le_two hc hcard hdeg hn hj hjq hja hnine
  have hy := h.last_degree_le_two hc hcard hn hj hjq hja hnine
  have hsum := hnine
  rw [h.arms_contacts] at hsum
  have hchoose : ∃ z w : V, (z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2) ∧
      degreeIn G w j ≤ degreeIn G z j ∧ 3 ≤ degreeIn G z j := by
    by_cases hle : degreeIn G (d 3) j ≤ degreeIn G (d 2) j
    · exact ⟨d 2, d 3, Or.inl ⟨rfl, rfl⟩, hle, by omega⟩
    · exact ⟨d 3, d 2, Or.inr ⟨rfl, rfl⟩, by omega, by omega⟩
  obtain ⟨z, w, hpair, hle, hthree⟩ := hchoose
  obtain ⟨v0, hv0⟩ := c.property.blocks_quad j hj
  obtain ⟨v, hv, hz⟩ := exists_three_included_labels v0 z (by rwa [hv0])
  have hvj := hv.trans hv0
  exact ⟨z, w, v, hpair, hle, hvj, hz,
    h.opposite_pair_bounds hc hcard hdeg hn hj hjq hja hnine hpos v hvj z w hpair hz⟩

end Erdos577.JointFinal

import ErdosProblems.Erdos577.JointFullExcluded

/-! Wang's local classification applies to every qualifying outside block
of the constructed core. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.local_conclusion {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) : Conclusion p q d j := by
  have hinit := h.initial_cases hc hcard hdeg hn hj hjq hja hnine
  by_cases hxzero : degreeIn G p.leaf j = 0
  · exact hinit.2.2 (Or.inl hxzero)
  by_cases hequal : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) = edgeCount G a
  · exact hinit.2.2 (Or.inr hequal)
  have hle := h.primary_le_original hc
  have hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a := by
    omega
  have hpos : 1 ≤ degreeIn G p.leaf j := by omega
  by_cases hfull : degreeIn G (d 2) j = 4 ∨ degreeIn G (d 3) j = 4
  · exact False.elim (h.full_distinguished_false hc hcard hdeg hn hloss
      hj hjq hja hnine hpos hfull)
  have hjcard := (c.property.blocks_quad j hj).card
  have hfirst := degreeIn_le_card G (d 2) j
  have hsecond := degreeIn_le_card G (d 3) j
  rw [hjcard] at hfirst hsecond
  have hnot := not_or.mp hfull
  exact h.three_distinguished_conclusion hc hcard hdeg hn hloss hj hjq hja hnine hpos
    (by omega) (by omega)

end Erdos577.JointFinal

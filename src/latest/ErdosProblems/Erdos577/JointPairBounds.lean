import ErdosProblems.Erdos577.JointPairCore

/-! All five opposite-pair bounds for every allowed distinguished order and cyclic labeling. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.opposite_pair_bounds {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hthree : ∀ i : Fin 4, i ≠ 3 → G.Adj z (v i)) :
    degreeIn G p.leaf {v 0, v 2} ≤ 1 ∧ degreeIn G p.leaf {v 1, v 3} ≤ 1 ∧
      degreeIn G (q 3) {v 0, v 2} ≤ 1 ∧ degreeIn G (q 3) {v 1, v 3} ≤ 1 ∧
      degreeIn G w {v 1, v 3} ≤ 1 := by
  have hrows := h.pair_rows hc hcard hdeg hn hj hjq hja hnine hpos v hv z w hpair hthree
  obtain ⟨hxL, hyL, hwL⟩ := hrows.low_pair_bounds
  have hhigh (u : V) (hu : u = p.leaf ∨ u = q 3) : degreeIn G u {v 0, v 2} ≤ 1 := by
    apply (degree_pair_le_one_iff u (v 0) (v 2) (v.injective.ne (by decide))).mpr
    rintro ⟨hu0, hu2⟩
    have hdiag := h.leaf_high_forces_diagonal hc hcard hdeg hn hj hjq hja
      v hv z w hpair hrows u hu hu0 hu2
    exact hrows.high_diagonal_false u hu hu0 hu2 hdiag
  exact ⟨hhigh p.leaf (Or.inl rfl), hxL, hhigh (q 3) (Or.inr rfl), hyL, hwL⟩

end Erdos577.JointFinal

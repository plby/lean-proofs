import ErdosProblems.Erdos577.SmallLeafClassification
import ErdosProblems.Erdos577.FirstPawLeafTwo

/-! Pattern (5) contradicts the common three-neighbor set forced by a small heavy leaf. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.not_first_paw_pattern5 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) : ¬PawBlock.Pattern5 p q := by
  intro h
  have hcenter := h.center_le_two p q
  change degreeIn G (p.vertices 1) q.support ≤ 2 at hcenter
  have hleaf : degreeIn G p.leaf q.support ≤ 2 := by
    have hh := q.degree_le_mask p.leaf 5 (by
      intro j hj
      rcases h.2.1 j (Or.inl hj) with rfl | rfl <;> decide)
    exact hh
  have hb3 : degreeIn G (p.vertices 2) q.support ≤ 3 := by
    have hh := q.degree_le_mask (p.vertices 2) 13 (by
      intro j hj
      have hn1 := h.2.2.1 j hj
      fin_cases j
      · decide
      · exact False.elim (hn1 rfl)
      · decide
      · decide)
    exact hh
  have hc3 : degreeIn G (p.vertices 3) q.support ≤ 3 := by
    have hh := q.degree_le_mask (p.vertices 3) 7 (by
      intro j hj
      have hn3 := h.2.2.2 j hj
      fin_cases j
      · decide
      · decide
      · decide
      · exact False.elim (hn3 rfl))
    exact hh
  have hsum := p.contacts_support q.support
  rw [p.contacts_triangle] at hsum
  have hpos : 0 < degreeIn G p.leaf q.support := by omega
  have hweighted : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support := by omega
  obtain ⟨_, s, _, hs3, hbset, hcset⟩ :=
    hc.small_leaf_precise hcard hdeg hn p hp hb q hq hleaf hpos hweighted
  have hb2 : degreeIn G (p.vertices 2) q.support ≤ 2 := by
    have hh := q.degree_le_mask (p.vertices 2) 5 (by
      intro j hj
      have hm : q j ∈ s := hbset ▸ mem_filter.mpr ⟨(q.mem_support _).mpr ⟨j, rfl⟩, hj⟩
      have hcj := (mem_filter.mp (hcset.symm ▸ hm)).2
      have hn1 := h.2.2.1 j hj
      have hn3 := h.2.2.2 j hcj
      fin_cases j
      · decide
      · exact False.elim (hn1 rfl)
      · decide
      · exact False.elim (hn3 rfl))
    exact hh
  change (q.support.filter (G.Adj (p.vertices 2))).card ≤ 2 at hb2
  rw [hbset, hs3] at hb2
  omega

end Erdos577

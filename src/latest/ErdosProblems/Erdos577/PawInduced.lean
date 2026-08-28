import ErdosProblems.Erdos577.Paws

/-! A paw remainder without a quadrilateral has neither additional leaf–triangle edge. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma Paw.nonadjacent_of_no_quad (p : Paw G) (hn : ¬QuadOn G p.support) :
    ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3) := by
  classical
  apply p.leaf_nonadjacent_of_degree_le_one
  by_contra hh
  have htwo : 2 ≤ degreeIn G p.leaf p.triangle := by omega
  have hq := QuadOn.of_triangle p.triangle_clique p.leaf_not_mem_triangle htwo
  rw [← p.support_eq] at hq
  exact hn hq

lemma Paw.leaf_triangle_degree_eq_one (p : Paw G) [DecidableRel G.Adj]
    (hn : ¬QuadOn G p.support) : degreeIn G p.leaf p.triangle = 1 := by
  obtain ⟨h2, h3⟩ := p.nonadjacent_of_no_quad hn
  rw [p.leaf_triangle_degree, if_neg h2, if_neg h3]

variable [Fintype V]

lemma TriangleChain.paw_nonadjacent (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) :
    ¬G.Adj p.leaf (p.vertices 2) ∧ ¬G.Adj p.leaf (p.vertices 3) := by
  exact p.nonadjacent_of_no_quad (by rw [hp]; exact c.no_quad_remainder hcard hn)

end Erdos577

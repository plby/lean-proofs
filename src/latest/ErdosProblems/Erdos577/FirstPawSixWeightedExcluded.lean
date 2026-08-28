import ErdosProblems.Erdos577.FirstPawSixWeightedLarge
import ErdosProblems.Erdos577.FirstPawSixWeightedSmall

/-! Both weighted branches exclude the last exact case (24) of Wang Lemma4.8. -/

namespace Erdos577.FirstPawSix.WeightedCase

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2)) : False := by
  obtain ⟨a, ha, hab, hweight⟩ := heavy_block hcard hdeg hn p hp hb q hq hd hdiag hrows
  by_cases hlarge : 7 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
      degreeIn G (p.vertices 3) a
  · exact large_three_false hc hcard hdeg hn p hp hb q hq hd hdiag hrows ha hab hweight hlarge
  · exact small_three_false hc hcard hdeg hn p hp hb q hq hd hdiag hrows ha hab hweight (by omega)

end Erdos577.FirstPawSix.WeightedCase

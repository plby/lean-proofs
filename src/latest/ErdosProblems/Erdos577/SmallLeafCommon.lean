import ErdosProblems.Erdos577.SmallLeafClassification
import ErdosProblems.Erdos577.PathColumnCount

/-! A small leaf and seven contacts force three common neighbors of the noncentral pair. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.small_leaf_common_three {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hsmall : degreeIn G p.leaf q.support ≤ 2)
    (hheavy : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support +
      degreeIn G (p.vertices 3) q.support) :
    3 ≤ ((q.support.filter (G.Adj (p.vertices 2))) ∩
      (q.support.filter (G.Adj (p.vertices 3)))).card := by
  by_cases hz : degreeIn G p.leaf q.support = 0
  · apply common_intersection_three q.support _ _ (filter_subset _ _) (filter_subset _ _)
      q.card_support
    change 7 ≤ degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support
    omega
  · obtain ⟨_, s, _, hs3, hbset, hcset⟩ := hc.small_leaf_precise hcard hdeg hn
      p hp hb q hq hsmall (by omega) hheavy
    rw [hbset, hcset, inter_self, hs3]

end Erdos577

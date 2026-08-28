import ErdosProblems.Erdos577.WeightedTwelveCompletion

/-! TeX9.65: the remaining weighted pattern12 is excluded without any later claim. -/

namespace Erdos577

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.not_weighted_pattern12 {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s) :
    ¬WeightedPawBlock.Pattern12 p q := by
  intro hpat
  obtain ⟨d, h⟩ := WeightedTwelve.exists_configuration hc hcard hdeg hn p hp hs q hq hpat
  exact h.impossible hc hcard hdeg hn

end Erdos577

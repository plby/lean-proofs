import ErdosProblems.Erdos577.FirstPawSixNormalization

/-! Any counterexample with pattern (6) gives an actual feasible chain
in case (22), (23), or (24). -/

namespace Erdos577.FirstPawSix

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem reduce_to_three_cases {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern6 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) :
    ∃ (d : TriangleChain G) (p' : Paw G) (q' : Quadrilateral G) (tag : Fin 3),
      d.Feasible ∧ p'.support = d.remainder ∧ q'.support ∈ d.blocks ∧
      Disjoint p'.support q'.support ∧ PawBlock.OnlyFirst q' ∧
      PawBlock.ExactRows p' q' (caseRows (Fin.castAdd 2 tag)) := by
  obtain ⟨tag, hrows⟩ := exact_cases hc hcard hdeg hn p hp hb q hq hd h hheavy
  fin_cases tag
  · exact ⟨c, p, q, 0, hc, hp, hq.symm ▸ hb, hd, h.1, hrows⟩
  · exact ⟨c, p, q, 1, hc, hp, hq.symm ▸ hb, hd, h.1, hrows⟩
  · exact ⟨c, p, q, 2, hc, hp, hq.symm ▸ hb, hd, h.1, hrows⟩
  · obtain ⟨d, p', q', hdf, hp', hq', hd', hdiag', hrows', _⟩ :=
      exists_normalized_chain hc hcard hn p hp hb q hq hd h.1 false hrows
    exact ⟨d, p', q', 2, hdf, hp', hq', hd', hdiag', hrows'⟩
  · obtain ⟨d, p', q', hdf, hp', hq', hd', hdiag', hrows', _⟩ :=
      exists_normalized_chain hc hcard hn p hp hb q hq hd h.1 true hrows
    exact ⟨d, p', q', 1, hdf, hp', hq', hd', hdiag', hrows'⟩

end Erdos577.FirstPawSix

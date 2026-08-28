import ErdosProblems.Erdos577.FirstPawSixWeightedHeavy
import ErdosProblems.Erdos577.FirstPawSixWeightedFactors
import ErdosProblems.Erdos577.IndexedInsertionBound
import ErdosProblems.Erdos577.PawTerminalExchange
import ErdosProblems.Erdos577.TerminalReplacements

/-! The heavy case24 block has at most two contacts from the original leaf. -/

namespace Erdos577.FirstPawSix.WeightedCase

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem leaf_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (hdiag : PawBlock.OnlyFirst q)
    (hrows : PawBlock.ExactRows p q (caseRows 2))
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (hweight : 13 ≤ FirstPawFour.weight p q a) : degreeIn G p.leaf a ≤ 2 := by
  by_contra! hlarge
  have hfour := degreeIn_le_card G p.leaf a
  rw [(c.property.blocks_quad a ha).card] at hfour
  have hfive : 5 ≤ contacts G ((vertexSet.erase 0).image (PawEncoding.labeling p q hd)) a := by
    rw [other_contacts]
    unfold FirstPawFour.weight at hweight
    omega
  have hno := no_universal_of_index_pairs (c.property.blocks_quad a ha)
    (PawEncoding.labeling p q hd) vertexSet 0 hfive
    (fun v hv w hw hvw ↦ no_leaf_pair hcard hn p hp hb q hq hd hdiag hrows ha hab v w hv hw hvw)
  exact hno (fun z hz ↦ (hc.presentPaw_feasible p hp).terminal_universal_replace ha hlarge hz)

end Erdos577.FirstPawSix.WeightedCase

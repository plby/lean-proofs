import ErdosProblems.Erdos577.TripleForbiddenChains
import ErdosProblems.Erdos577.NeighborRowBounds
import ErdosProblems.Erdos577.CommonTriple
import ErdosProblems.Erdos577.MatchingGain

/-! The common row argument for U and V, using the proved matching-score obstruction. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.four_rows_extra_le_two {c : TriangleChain G} (hc : c.Feasible)
    {j : Finset V} (hj : j ∈ c.blocks) (x y z : V)
    (hheavy : 9 ≤ degreeIn G x j + degreeIn G y j + degreeIn G z j + degreeIn G c.terminal j)
    (hxy : ¬CommonReplacement G x y c.terminal j)
    (hxz : ¬CommonReplacement G x z c.terminal j)
    (hyz : ¬CommonReplacement G y z c.terminal j) : degreeIn G c.terminal j ≤ 2 := by
  by_contra hlarge
  have hrep : ∀ u ∈ j, QuadOn G (insert c.terminal (j.erase u)) :=
    fun _ hu ↦ hc.terminal_universal_replace hj (by omega) hu
  have hthree := degree_triple_le_card x y z j
    (no_common_of_universal_insertion x y c.terminal j hxy hrep)
    (no_common_of_universal_insertion x z c.terminal j hxz hrep)
    (no_common_of_universal_insertion y z c.terminal j hyz hrep)
  have hrow := degreeIn_le_card G c.terminal j
  have hfour := (c.property.blocks_quad j hj).card
  omega

theorem TriangleChain.Feasible.common_triple_of_four_rows {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {j : Finset V} (hj : j ∈ c.blocks)
    (z : V) (hz : z ∉ p.support ∪ j) (hsmall : degreeIn G z j ≤ 2)
    (hheavy : 9 ≤ degreeIn G p.leaf j + degreeIn G (p.vertices 2) j +
      degreeIn G (p.vertices 3) j + degreeIn G z j)
    (hno : ¬CommonReplacement G (p.vertices 2) (p.vertices 3) z j) :
    degreeIn G p.leaf j + degreeIn G (p.vertices 2) j +
      degreeIn G (p.vertices 3) j + degreeIn G z j = 9 ∧
      ∃ d : Quadrilateral G, d.support = j ∧
        (∀ i : Fin 4, i ≠ 0 → G.Adj (p.vertices 2) (d i) ∧ G.Adj (p.vertices 3) (d i)) ∧
        G.Adj z (d 2) := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad j hj
  have hweight : 7 ≤ degreeIn G p.leaf j + degreeIn G (p.vertices 2) j +
      degreeIn G (p.vertices 3) j := by omega
  have hcases :
      (degreeIn G p.leaf q.support = 1 ∧ degreeIn G (p.vertices 2) q.support = 3 ∧
        ∀ v ∈ q.support, G.Adj (p.vertices 2) v ↔ G.Adj (p.vertices 3) v) ∨
      (degreeIn G p.leaf q.support = 0 ∧
        7 ≤ degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support) := by
    rw [hq]
    rcases hc.claim_two_five hcard hdeg hn p hp hj hweight with hzero | ⟨hone, hsum, heq⟩
    · exact Or.inr ⟨hzero, by omega⟩
    · have hdegrees : degreeIn G (p.vertices 2) j = degreeIn G (p.vertices 3) j :=
        congrArg Finset.card heq
      refine Or.inl ⟨hone, by omega, ?_⟩
      intro v hv
      have hmem := Finset.ext_iff.mp heq v
      simpa only [mem_filter, hv, true_and] using hmem
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hgain : ¬TwoEdgeReduction G (p.support ∪ q.support) (edgeCount G q.support + 2) := by
    rw [hp, hq]
    exact hc.no_two_edge_gain hcard hdeg hn hj
  obtain ⟨hsum, d, hdq, hrows, hz2⟩ := p.common_triple q hd z (by rwa [hq])
    (by rwa [hq]) hgain (by rwa [hq]) hcases
  exact ⟨by simpa only [hq] using hsum, d, hdq.trans hq, hrows, hz2⟩

end Erdos577

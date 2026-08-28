import ErdosProblems.Erdos577.ClaimTwoSeven

/-! Claims2.5--2.7 contradict the exact doubled-leaf degree sum. -/

namespace Erdos577

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.doubled_leaf_block_le_eight {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks) :
    2 * degreeIn G p.leaf s + degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s ≤ 8 := by
  have hx4 := degreeIn_le_card G p.leaf s
  have hb4 := degreeIn_le_card G (p.vertices 2) s
  have ht4 := degreeIn_le_card G (p.vertices 3) s
  rw [(c.property.blocks_quad s hs).card] at hx4 hb4 ht4
  by_cases hfour : degreeIn G p.leaf s = 4
  · obtain ⟨h2, h3⟩ := hc.claim_two_six hcard hdeg hn p hp hs hfour
    omega
  by_cases hthree : degreeIn G p.leaf s = 3
  · have hh := hc.claim_two_seven hcard hdeg hn p hp hs hthree
    omega
  have hsmall : degreeIn G p.leaf s ≤ 2 := by omega
  by_contra hlarge
  have hh : 7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 2) s +
      degreeIn G (p.vertices 3) s := by omega
  rcases hc.claim_two_five hcard hdeg hn p hp hs hh with hz | ⟨hone, hsix, _⟩
  · omega
  · omega

theorem TriangleChain.Feasible.false_of_minimum_degree {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) : False := by
  obtain ⟨s, hs, hheavy⟩ := c.exists_doubled_leaf_heavy hcard hdeg hn p hp
  have hbound := hc.doubled_leaf_block_le_eight hcard hdeg hn p hp hs
  omega

theorem TriangleChain.Strong.false_of_minimum_degree {c : TriangleChain G}
    (hc : c.Strong) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k) : False := by
  obtain ⟨p, _, _, hp⟩ := hc.exists_paw
  exact hc.toFeasible.false_of_minimum_degree hcard hdeg hn p hp

end Erdos577

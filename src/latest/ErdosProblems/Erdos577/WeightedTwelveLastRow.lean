import ErdosProblems.Erdos577.WeightedTwelveInsertions

/-! The exposed row has at most two contacts in the second heavy block. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Configuration.last_not_universal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d)
    {j : Finset V} (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hjd : j ≠ d.support)
    (hnine : 9 ≤ contacts G (JointFinal.arms p q d) j) :
    ¬(∀ u ∈ j, QuadOn G (insert (q 3) (j.erase u))) := by
  intro hrep
  obtain ⟨_, hx1, hx2, _, _, h12⟩ := JointCore.four_distinct h.arms_card
  have hx : p.leaf ∈ JointFinal.spokes p d := by simp [JointFinal.spokes]
  have h1 : d 2 ∈ JointFinal.spokes p d := by simp [JointFinal.spokes]
  have h2 : d 3 ∈ JointFinal.spokes p d := by simp [JointFinal.spokes]
  have hno1 := h.no_exposed_common hc hcard hn hj hjq hjd hx h1 hx1
  have hno2 := h.no_exposed_common hc hcard hn hj hjq hjd hx h2 hx2
  have hno12 := h.no_exposed_common hc hcard hn hj hjq hjd h1 h2 h12
  have hbound := degree_triple_le_card p.leaf (d 2) (d 3) j
    (no_common_of_universal_insertion _ _ _ _ hno1 hrep)
    (no_common_of_universal_insertion _ _ _ _ hno2 hrep)
    (no_common_of_universal_insertion _ _ _ _ hno12 hrep)
  have hy := degreeIn_le_card G (q 3) j
  rw [(c.property.blocks_quad j hj).card] at hbound hy
  rw [h.arms_contacts] at hnine
  omega

theorem Configuration.last_degree_le_two {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d)
    {j : Finset V} (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hjd : j ≠ d.support)
    (hnine : 9 ≤ contacts G (JointFinal.arms p q d) j) : degreeIn G (q 3) j ≤ 2 := by
  by_contra hlarge
  obtain ⟨e, he, ht, _, _, _, _, _, _, _, hkeep⟩ := exists_swap hc hcard hn
    p h.paw h.first q rfl (h.paw_disjoint h.first) h.pattern
  apply h.last_not_universal hc hcard hn hj hjq hjd hnine
  intro u hu
  have hthree : 3 ≤ degreeIn G e.terminal j := by rw [ht]; omega
  have hrep := he.toFeasible.terminal_universal_replace (hkeep j hj hjq).1 hthree hu
  rwa [ht] at hrep

end Erdos577.WeightedTwelve

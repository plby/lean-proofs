import ErdosProblems.Erdos577.LargeLeafThreeLocal

/-! Every other block has at most ten triangle contacts in the three-leaf case. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_dense_false_ordered {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    (hb : 2 ≤ degreeIn G (p.vertices 2) s)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) (hT : 11 ≤ contacts G p.triangle a) :
    False := by
  obtain ⟨q0, hq0⟩ := c.property.blocks_quad s hs
  obtain ⟨q, hq, hrow⟩ := q0.exists_three_contact_labels p.leaf (by rwa [hq0])
  have hqs : q.support = s := hq.trans hq0
  apply three_no_compatible_false hc hcard hdeg hn p hp hs q hqs (by rwa [hqs]) hrow
    (by rwa [hqs]) (by rwa [hqs])
  intro z hz hquad hscore
  rw [hqs] at hz hquad hscore ⊢
  exact three_dense_no_compatible hc hcard hdeg hn p hp hs hthree hnon ha has hT z hz hquad hscore

theorem three_triangle_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) : contacts G p.triangle a ≤ 10 := by
  by_contra hh
  have hT : 11 ≤ contacts G p.triangle a := by omega
  by_cases hb : 2 ≤ degreeIn G (p.vertices 2) s
  · exact three_dense_false_ordered hc hcard hdeg hn p hp hs hthree hnon hb ha has hT
  · apply three_dense_false_ordered hc hcard hdeg hn p.swapNoncentral
      (by rw [Paw.swapNoncentral_support, hp]) hs
      (by simpa only [Paw.swapNoncentral_leaf] using hthree) ?_ ?_ ha has
      (by rw [Paw.swapNoncentral_triangle]; exact hT)
    · simp only [Paw.swapNoncentral_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      omega
    · simp only [Paw.swapNoncentral_apply, Equiv.swap_apply_left]
      omega

theorem three_occupied_inside_ge_five {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    (z : V) (hz : z ∈ s) (hadj : G.Adj z (p.vertices 2) ∨ G.Adj z (p.vertices 3))
    (hquad : QuadOn G (insert p.leaf (s.erase z)))
    (hscore : edgeCount G (insert p.leaf (s.erase z)) = edgeCount G s) :
    5 ≤ degreeIn G z (p.support ∪ s) := by
  by_contra hsmall
  have hFS : Disjoint p.support s := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hzout : z ∉ p.support := fun hh ↦ disjoint_left.mp hFS hh hz
  have hfive : (insert z p.support).card = 5 := by
    rw [card_insert_of_notMem hzout, p.card_support]
  have hFF : contacts G p.support p.support = 8 := by
    rw [contacts_self_eq_twice_edgeCount G,
      p.edgeCount_of_no_quad (by rw [hp]; exact c.no_quad_remainder hcard hn)]
  have htriangle := JointClaims.triangle_contacts_le_four hc hcard hn p hp hs (by omega)
  have hF : contacts G p.support (p.support ∪ s) ≤ 15 := by
    rw [contacts_union_right G _ hFS, p.contacts_support s]
    omega
  have hinside : contacts G (insert z p.support) (c.remainder ∪ s) ≤ 19 := by
    rw [← hp, contacts, sum_insert hzout]
    change degreeIn G z (p.support ∪ s) + contacts G p.support (p.support ∪ s) ≤ 19
    omega
  obtain ⟨a, ha, has, hweight⟩ := c.exists_eleven_contact_outside_core
    hcard hdeg hs (insert z p.support) hfive hinside
  have hlink := noncentral_link hc hcard hn p hp hs (by omega) z hz hadj
  have hT := (hc.leaf_transport hcard hdeg hn p hp hs ha has z hz hlink hweight
    (Or.inl ⟨hquad, hscore⟩)).2.2
  have hbound := three_triangle_bound hc hcard hdeg hn p hp hs hthree hnon ha has
  omega

end Erdos577.LargeLeaf

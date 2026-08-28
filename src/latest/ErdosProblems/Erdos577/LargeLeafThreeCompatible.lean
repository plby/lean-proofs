import ErdosProblems.Erdos577.LargeLeafThreeReplacements

/-! A dense outside block forbids every compatible score-preserving first-block replacement. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem three_dense_no_compatible {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) (hT : 11 ≤ contacts G p.triangle a)
    (z : V) (hz : z ∈ s) (hquad : QuadOn G (insert p.leaf (s.erase z)))
    (hscore : edgeCount G (insert p.leaf (s.erase z)) = edgeCount G s) :
    ¬QuadOn G (insert (p.vertices 2) (s.erase z)) := by
  intro hb
  obtain ⟨hcl, _, _⟩ := dense_core_bounds hc hcard hn p hp hs (by omega) ha has hT
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  obtain ⟨d, hd, hcenter, hprimary, hsecondary⟩ := dense_pair_labels p hcl hFA hT
  have hpair : WeightedTwelve.DensePair p d := by
    have hdis : Disjoint p.support d.support := by rwa [hd]
    refine ⟨hdis, ?_, ?_, hcenter 2 (by decide), hcenter 3 (by decide), ?_⟩
    · rwa [hd]
    · rwa [hd]
    · rw [JointFinal.primary_support_eq p d hdis]
      exact hprimary
  have h : DenseObstruction.PairConfig c p d s z :=
    ⟨hp, hs, by rwa [hd], by rwa [hd], hz, hpair, hquad, hscore, hb⟩
  have hrev := h.reverse (hcenter 1 (by decide)) hsecondary
  have hfirst := three_pair_inside hc hcard hn h hthree hnon
  have hsecond := three_pair_inside hc hcard hn hrev hthree hnon
  rw [d.reverse_support] at hsecond
  exact h.false_of_two_inside_bounds hc hcard hdeg hn (hcenter 1 (by decide)) hsecondary
    hfirst hsecond

end Erdos577.LargeLeaf

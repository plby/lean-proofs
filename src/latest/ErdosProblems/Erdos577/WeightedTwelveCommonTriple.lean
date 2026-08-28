import ErdosProblems.Erdos577.WeightedTwelveSmallTriple

/-! The actual exchanged chain supplies every hypothesis of the common-triple lemma. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Configuration.common_triple {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d)
    {j : Finset V} (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hjd : j ≠ d.support)
    (hnine : 9 ≤ contacts G (JointFinal.arms p q d) j) : JointFinal.Conclusion p q d j := by
  obtain ⟨e, he, _, _, hp', _, _, _, hkeep⟩ :=
    h.pair.exists_pair_chain hc hcard hn p h.paw d h.core
  let p' := h.pair.pairPaw
  have heJ := hkeep j hj hjd
  obtain ⟨v, hv⟩ := c.property.blocks_quad j hj
  have hxsmall := h.leaf_degree_le_two hc hcard hdeg hn hj hjq hjd hnine
  have hysmall := h.last_degree_le_two hc hcard hn hj hjq hjd hnine
  have hsum := hnine
  rw [h.arms_contacts] at hsum
  have hheavy : 7 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
      degreeIn G (p'.vertices 3) v.support := by
    rw [hv]
    change 7 ≤ degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j
    omega
  have hcases :
      (degreeIn G p'.leaf v.support = 1 ∧ degreeIn G (p'.vertices 2) v.support = 3 ∧
        ∀ u ∈ v.support, G.Adj (p'.vertices 2) u ↔ G.Adj (p'.vertices 3) u) ∨
      (degreeIn G p'.leaf v.support = 0 ∧
        7 ≤ degreeIn G (p'.vertices 2) v.support + degreeIn G (p'.vertices 3) v.support) := by
    by_cases hz : degreeIn G p'.leaf v.support = 0
    · exact Or.inr ⟨hz, by omega⟩
    · obtain ⟨hxone, s, _, hs3, hs1, hs2⟩ := he.toFeasible.small_leaf_precise
        hcard hdeg hn p' hp' heJ v hv (by rw [hv]; exact hxsmall) (by omega) hheavy
      have hthree : degreeIn G (p'.vertices 2) v.support = 3 :=
        (congrArg Finset.card hs1).trans hs3
      refine Or.inl ⟨hxone, hthree, ?_⟩
      intro u hu
      have hfilters := hs1.trans hs2.symm
      have hm := (congrArg (fun t : Finset V ↦ u ∈ t) hfilters).to_iff
      simpa only [mem_filter, hu, true_and] using hm
  have hdis : Disjoint p'.support v.support := by
    rw [hp', hv]
    exact e.property.remainder_disjoint.mono_right (e.blockPartition.block_subset heJ)
  have hFQ : Disjoint p'.support q.support := by
    rw [hp']
    exact e.property.remainder_disjoint.mono_right
      (e.blockPartition.block_subset (hkeep q.support h.first h.different.symm))
  have hym : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hyout : q 3 ∉ p'.support ∪ v.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp hFQ hh hym
    · rw [hv] at hh
      exact disjoint_left.mp (c.property.blocks_disjoint h.first hj hjq.symm) hym hh
  have hno := h.no_exposed_common hc hcard hn hj hjq hjd
    (u := d 2) (v := d 3) (by simp [JointFinal.spokes]) (by simp [JointFinal.spokes])
    (d.injective.ne (by decide))
  have hgain : ¬TwoEdgeReduction G (p'.support ∪ v.support) (edgeCount G v.support + 2) := by
    rw [hp', hv]
    exact he.toFeasible.no_two_edge_gain hcard hdeg hn heJ
  have hnine' : 9 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
      degreeIn G (p'.vertices 3) v.support + degreeIn G (q 3) v.support := by
    rw [hv]
    change 9 ≤ degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j + degreeIn G (q 3) j
    omega
  obtain ⟨hexact, w, hw, hcommon, hyw⟩ := p'.common_triple v hdis (q 3) hyout
    (by rw [hv]; exact hno) hgain hnine' hcases
  rw [hv] at hexact
  change degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j + degreeIn G (q 3) j = 9
    at hexact
  refine ⟨?_, w, hw.trans hv, hcommon, hyw⟩
  rw [h.arms_contacts]
  omega

end Erdos577.WeightedTwelve

import ErdosProblems.Erdos577.JointFinalPairExchange

/-! The equal-score core exchange supplies every hypothesis of the common-triple lemma. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.equal_core_conclusion {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 0 < degreeIn G p.leaf j)
    (he : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) = edgeCount G a) :
    Conclusion p q d j := by
  obtain ⟨e, heStrong, hp', _, _, hkeep⟩ := h.exists_equal_pair_chain hc hcard hn he
  let p' := h.pairPaw
  have heJ := hkeep j hj hja
  have hxsmall := h.leaf_degree_le_two hc hcard hdeg hn hj hjq hja hnine
  have hysmall := h.last_degree_le_two hc hcard hn hj hjq hja hnine
  have hsum := hnine
  rw [h.arms_contacts] at hsum
  obtain ⟨jq, hjq'⟩ := c.property.blocks_quad j hj
  have hsmall : degreeIn G p'.leaf jq.support ≤ 2 := by rw [hjq']; exact hxsmall
  have hpositive : 0 < degreeIn G p'.leaf jq.support := by rw [hjq']; exact hpos
  have hheavy : 7 ≤ degreeIn G p'.leaf jq.support + degreeIn G (p'.vertices 2) jq.support +
      degreeIn G (p'.vertices 3) jq.support := by
    rw [hjq']
    change 7 ≤ degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j
    omega
  obtain ⟨hxone, s, _, hs3, hs1, hs2⟩ := heStrong.toFeasible.small_leaf_precise
    hcard hdeg hn p' hp' heJ jq hjq' hsmall hpositive hheavy
  have hthree : degreeIn G (p'.vertices 2) jq.support = 3 :=
    (congrArg Finset.card hs1).trans hs3
  have hrows : ∀ v ∈ jq.support, G.Adj (p'.vertices 2) v ↔ G.Adj (p'.vertices 3) v := by
    intro v hv
    have hfilters := hs1.trans hs2.symm
    have hm := (congrArg (fun t : Finset V ↦ v ∈ t) hfilters).to_iff
    simpa only [mem_filter, hv, true_and] using hm
  have hdis : Disjoint p'.support jq.support := by
    rw [hp', hjq']
    exact e.property.remainder_disjoint.mono_right (e.blockPartition.block_subset heJ)
  have hYQ : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hybase : q 3 ∉ p.support ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp (h.paw_disjoint h.config.2.1) hh hYQ
    · exact disjoint_left.mp
        (c.property.blocks_disjoint h.config.2.2.1 h.config.2.1 h.config.2.2.2.1) hh hYQ
  have hsub : p'.support ⊆ p.support ∪ a := by
    rw [h.pairPaw_support]
    exact insert_subset (mem_union_left _ (p.support_eq ▸ mem_insert_self _ _))
      (insert_subset (mem_union_left _ ((mem_tupleSupport p.vertices _).mpr ⟨1, rfl⟩))
        (insert_subset (mem_union_right _ (h.mem 2))
          (singleton_subset_iff.mpr (mem_union_right _ (h.mem 3)))))
  have hyout : q 3 ∉ p'.support ∪ jq.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact hybase (hsub hh)
    · rw [hjq'] at hh
      exact disjoint_left.mp (c.property.blocks_disjoint h.config.2.1 hj hjq.symm) hYQ hh
  have hno := h.no_exposed_common hc hcard hn hj hjq hja
    (u := d 2) (v := d 3) (by simp [spokes]) (by simp [spokes])
    (d.injective.ne (by decide))
  have hgain : ¬TwoEdgeReduction G (p'.support ∪ jq.support) (edgeCount G jq.support + 2) := by
    rw [hp', hjq']
    exact heStrong.toFeasible.no_two_edge_gain hcard hdeg hn heJ
  have hnine' : 9 ≤ degreeIn G p'.leaf jq.support + degreeIn G (p'.vertices 2) jq.support +
      degreeIn G (p'.vertices 3) jq.support + degreeIn G (q 3) jq.support := by
    rw [hjq']
    change 9 ≤ degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j + degreeIn G (q 3) j
    omega
  obtain ⟨hexact, v, hv, hcommon, hyv⟩ := p'.common_triple jq hdis (q 3) hyout
    (by rwa [hjq']) hgain hnine' (Or.inl ⟨hxone, hthree, hrows⟩)
  rw [hjq'] at hexact
  change degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j + degreeIn G (q 3) j = 9
    at hexact
  refine ⟨?_, v, hv.trans hjq', hcommon, hyv⟩
  rw [h.arms_contacts]
  omega

theorem Core.initial_cases {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) :
    degreeIn G p.leaf j ≤ 2 ∧ degreeIn G (q 3) j ≤ 2 ∧
      (degreeIn G p.leaf j = 0 ∨
        edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) = edgeCount G a →
        Conclusion p q d j) := by
  refine ⟨h.leaf_degree_le_two hc hcard hdeg hn hj hjq hja hnine,
    h.last_degree_le_two hc hcard hn hj hjq hja hnine, ?_⟩
  rintro (hzero | he)
  · exact h.zero_leaf_conclusion hc hcard hn hj hjq hja hnine hzero
  · by_cases hzero : degreeIn G p.leaf j = 0
    · exact h.zero_leaf_conclusion hc hcard hn hj hjq hja hnine hzero
    · exact h.equal_core_conclusion hc hcard hdeg hn hj hjq hja hnine
        (Nat.pos_of_ne_zero hzero) he

end Erdos577.JointFinal

import ErdosProblems.Erdos577.DensePairLastRow

/-! The actual exchanged chain supplies every hypothesis of the common-triple lemma. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Conclusion (p : Paw G) (d : Quadrilateral G) (z : V) (j : Finset V) : Prop :=
  contacts G (JointBridge.arms p z (d 2) (d 3)) j = 9 ∧
    ∃ v : Quadrilateral G, v.support = j ∧
      (∀ i : Fin 4, i ≠ 0 → G.Adj (d 2) (v i) ∧ G.Adj (d 3) (v i)) ∧ G.Adj z (v 2)

theorem PairConfig.common_triple {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hjd : j ≠ d.support)
    (hnine : 9 ≤ contacts G (JointBridge.arms p z (d 2) (d 3)) j) : Conclusion p d z j := by
  obtain ⟨e, he, _, _, hp', _, _, _, hkeep⟩ :=
    h.pair.exists_pair_chain hc hcard hn p h.paw d h.core
  let p' := h.pair.pairPaw
  have heJ := hkeep j hj hjd
  obtain ⟨v, hv⟩ := c.property.blocks_quad j hj
  have hysmall := h.last_degree_le_two hc hcard hn hj hjs hjd hnine
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
    have hh := he.toFeasible.claim_two_five hcard hdeg hn p' hp' heJ
      (by rwa [hv] at hheavy)
    rw [← hv] at hh
    rcases hh with hxzero | ⟨hxone, hsum6, hfilters⟩
    · exact Or.inr ⟨hxzero, by omega⟩
    · have hdegrees : degreeIn G (p'.vertices 2) v.support =
          degreeIn G (p'.vertices 3) v.support := congrArg Finset.card hfilters
      refine Or.inl ⟨hxone, by omega, ?_⟩
      intro u hu
      have hm := (congrArg (fun t : Finset V ↦ u ∈ t) hfilters).to_iff
      simpa only [mem_filter, hu, true_and] using hm
  have hdis : Disjoint p'.support v.support := by
    rw [hp', hv]
    exact e.property.remainder_disjoint.mono_right (e.blockPartition.block_subset heJ)
  have hFQ : Disjoint p'.support s := by
    rw [hp']
    exact e.property.remainder_disjoint.mono_right
      (e.blockPartition.block_subset (hkeep s h.first h.different.symm))
  have hym : z ∈ s := h.exposed
  have hyout : z ∉ p'.support ∪ v.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp hFQ hh hym
    · rw [hv] at hh
      exact disjoint_left.mp (c.property.blocks_disjoint h.first hj hjs.symm) hym hh
  have hno := h.no_exposed_common hc hcard hn hj hjs hjd
    (u := d 2) (v := d 3) (by simp [JointFinal.spokes]) (by simp [JointFinal.spokes])
    (d.injective.ne (by decide))
  have hgain : ¬TwoEdgeReduction G (p'.support ∪ v.support) (edgeCount G v.support + 2) := by
    rw [hp', hv]
    exact he.toFeasible.no_two_edge_gain hcard hdeg hn heJ
  have hnine' : 9 ≤ degreeIn G p'.leaf v.support + degreeIn G (p'.vertices 2) v.support +
      degreeIn G (p'.vertices 3) v.support + degreeIn G z v.support := by
    rw [hv]
    change 9 ≤ degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j + degreeIn G z j
    omega
  obtain ⟨hexact, w, hw, hcommon, hyw⟩ := p'.common_triple v hdis z hyout
    (by rw [hv]; exact hno) hgain hnine' hcases
  rw [hv] at hexact
  change degreeIn G p.leaf j + degreeIn G (d 2) j + degreeIn G (d 3) j + degreeIn G z j = 9
    at hexact
  refine ⟨?_, w, hw.trans hv, hcommon, hyw⟩
  rw [h.arms_contacts]
  omega

end Erdos577.DenseObstruction

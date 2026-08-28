import ErdosProblems.Erdos577.DensePairAverages

/-! Five actual four-cycles complete the contradiction, retaining every unselected block. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem PairConfig.two_classified_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    {j b : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hjd : j ≠ d.support)
    (hb : b ∈ c.blocks) (hbs : b ≠ s) (hbd : b ≠ d.support) (hbj : b ≠ j)
    (hfirst : Conclusion p d z j) (hsecond : Conclusion p d.reverse z b) : False := by
  obtain ⟨_, v, hv, hrows1, hy1⟩ := hfirst
  obtain ⟨_, w, hw, hrows2, hy2⟩ := hsecond
  change ∀ i : Fin 4, i ≠ 0 → G.Adj (d 2) (w i) ∧ G.Adj (d 1) (w i) at hrows2
  have hyout (a : Finset V) (ha : a ∈ c.blocks) (has : a ≠ s) : z ∉ a :=
    fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint h.first ha has.symm) h.exposed hh
  have parts := JointFinal.two_classified_partition d v w z
    (by rw [hv]; exact c.property.blocks_disjoint h.core hj hjd.symm)
    (by rw [hw]; exact c.property.blocks_disjoint h.core hb hbd.symm)
    (by rw [hv, hw]; exact c.property.blocks_disjoint hj hb hbj.symm)
    (hyout d.support h.core h.different)
    (by rw [hv]; exact hyout j hj hjs) (by rw [hw]; exact hyout b hb hbs)
    hrows1 hrows2 hy1 hy2
  obtain ⟨e, _, ht, htri, _, _, hkeep⟩ := h.exposed_chain hc
  have hTA : Disjoint p.triangle d.support :=
    h.pair.disjoint.mono_left (p.support_eq ▸ subset_insert _ _)
  have hrem : QuadOn G ((e.triangle ∪ d.support) \ {d 1, d 2, d 3}) := by
    rw [htri, JointFinal.last_three_core_complement p d hTA]
    exact h.last_triangle_quad
  have hm (i : Fin 4) : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have hused : ({d 1, d 2, d 3} : Finset V) ⊆ e.triangle ∪ d.support :=
    insert_subset (mem_union_right _ (hm 1)) (insert_subset (mem_union_right _ (hm 2))
      (singleton_subset_iff.mpr (mem_union_right _ (hm 3))))
  have hsel : ({j, b} : Finset (Finset V)) ⊆ e.blocks :=
    insert_subset (hkeep j hj hjs) (singleton_subset_iff.mpr (hkeep b hb hbs))
  have hna : d.support ∉ ({j, b} : Finset (Finset V)) := by
    simpa only [mem_insert, mem_singleton, not_or] using And.intro hjd.symm hbd.symm
  have hf : Nonempty (BlockPartition G
      (insert e.terminal ({d 1, d 2, d 3} ∪ ({j, b} : Finset (Finset V)).biUnion id))) := by
    simpa only [ht, hv, hw, biUnion_insert, singleton_biUnion, id_eq, union_assoc] using parts
  exact hn (e.hasPacking_of_selected_core hcard (hkeep d.support h.core h.different)
    {j, b} hsel hna hused hrem hf)

end Erdos577.DenseObstruction

import ErdosProblems.Erdos577.WeightedTwelveFinalFactor

/-! The final two cycles complete through the dense core and the actual exposed first block. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Configuration.final_partial_factor {c : TriangleChain G}
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d)
    {j : Finset V} (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hjd : j ≠ d.support)
    (hcon : JointFinal.Conclusion p q d j) :
    LocalFactor G (insert (q 3) ({p.vertices 3, d 2, d 3} ∪ j)) := by
  obtain ⟨_, v, hv, hrows, hyv⟩ := hcon
  have hDJ : Disjoint d.support j := c.property.blocks_disjoint h.core hj hjd.symm
  have hDQ : Disjoint d.support q.support := c.property.blocks_disjoint h.core h.first h.different
  have hm (i : Fin 4) : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have hb : p.vertices 3 ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩
  have hym : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hyb : G.Adj (q 3) (p.vertices 3) := (first_rows p q h.pattern).2.symm
  have hyd (i : Fin 4) : q 3 ≠ d i := fun he ↦ disjoint_left.mp hDQ (hm i) (he ▸ hym)
  have hbd (i : Fin 4) : p.vertices 3 ≠ d i := fun he ↦
    disjoint_left.mp h.pair.disjoint hb (he.symm ▸ hm i)
  have hfour : ({q 3, p.vertices 3, d 2, d 3} : Finset V).card = 4 :=
    card_eq_four.mpr ⟨q 3, p.vertices 3, d 2, d 3, hyb.ne, hyd 2, hyd 3, hbd 2, hbd 3,
      d.injective.ne (by decide), rfl⟩
  have hdis : Disjoint ({q 3, p.vertices 3, d 2, d 3} : Finset V) v.support := by
    rw [hv]
    exact disjoint_insert_left.mpr
      ⟨fun hh ↦ disjoint_left.mp (c.property.blocks_disjoint h.first hj hjq.symm) hym hh,
        disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp (h.paw_disjoint hj) hb hh,
          disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hDJ (hm 2) hh,
            disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hDJ (hm 3) hh)⟩⟩⟩
  have hf := final_factor_either v (q 3) (p.vertices 3) (d 2) (d 3) hfour hdis hyb
    h.pair.third_meets_pair hrows hyv
  rwa [hv] at hf

theorem Configuration.impossible {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d) : False := by
  obtain ⟨j, hj, hjq, hjd, hnine⟩ := h.exists_second_heavy hc hcard hdeg hn
  have hf := h.final_partial_factor hj hjq hjd (h.common_triple hc hcard hdeg hn hj hjq hjd hnine)
  have hFQ := h.paw_disjoint h.first
  obtain ⟨e, _, _, _, hp', _, _, _, _, _, hkeep⟩ :=
    exists_swap hc hcard hn p h.paw h.first q rfl hFQ h.pattern
  let p' := exposedPaw p q hFQ h.pattern
  have htri : p'.triangle = p.triangle := exposedPaw_triangle p q hFQ h.pattern
  have hm (i : Fin 4) : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have hb : p.vertices 3 ∈ p.triangle := by simp [Paw.triangle]
  have hbd (i : Fin 4) : p.vertices 3 ≠ d i := fun he ↦ disjoint_left.mp h.pair.disjoint
    ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩) (he.symm ▸ hm i)
  have hTA : Disjoint p.triangle d.support :=
    h.pair.disjoint.mono_left (p.support_eq ▸ subset_insert _ _)
  have hrem : QuadOn G ((p'.triangle ∪ d.support) \ {p.vertices 3, d 2, d 3}) := by
    rw [htri]
    exact JointCore.dense_complement_triple p.triangle_clique h.pair.complete hTA h.pair.dense
      (p.vertices 3) (d 2) (d 3) (mem_union_left _ hb) (mem_union_right _ (hm 2))
      (mem_union_right _ (hm 3)) (hbd 2) (hbd 3) (d.injective.ne (by decide))
  have hu : ({p.vertices 3, d 2, d 3} : Finset V) ⊆ p'.triangle ∪ d.support := by
    rw [htri]
    exact insert_subset (mem_union_left _ hb) (insert_subset (mem_union_right _ (hm 2))
      (singleton_subset_iff.mpr (mem_union_right _ (hm 3))))
  exact hn (JointCore.hasPacking_of_partial_core hcard p' hp'
    (hkeep d.support h.core h.different).1 (hkeep j hj hjq).1 hjd.symm hu hrem hf.partition)

end Erdos577.WeightedTwelve

import ErdosProblems.Erdos577.DensePairReversed

/-! The two inside estimates force distinct outside blocks; classification is universal first. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem PairConfig.exists_heavy_block {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    (hinside : contacts G (JointBridge.arms p z (d 2) (d 3))
      (p.support ∪ s ∪ d.support) ≤ 22) :
    ∃ j ∈ c.blocks, j ≠ s ∧ j ≠ d.support ∧
      9 ≤ contacts G (JointBridge.arms p z (d 2) (d 3)) j := by
  have hsel : ({s, d.support} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr h.core)
  have he : c.remainder ∪ ({s, d.support} : Finset (Finset V)).biUnion id =
      p.support ∪ s ∪ d.support := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← h.paw, union_assoc]
  obtain ⟨j, hj, hjn, hnine⟩ := JointFirst.exists_nine_outside_two hcard hdeg {s, d.support}
    hsel (card_pair_eq_two_iff.mpr h.different.symm) (JointBridge.arms p z (d 2) (d 3))
    h.arms_card (he.symm ▸ hinside)
  simp only [mem_insert, mem_singleton, not_or] at hjn
  exact ⟨j, hj, hjn.1, hjn.2, hnine⟩

theorem PairConfig.exists_second_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z)
    (hinside : contacts G (JointBridge.arms p z (d 2) (d 3))
      (p.support ∪ s ∪ d.support) ≤ 22)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hjd : j ≠ d.support) :
    ∃ b ∈ c.blocks, b ≠ s ∧ b ≠ d.support ∧ b ≠ j ∧
      9 ≤ contacts G (JointBridge.arms p z (d 2) (d 3)) b := by
  have hJ : contacts G (JointBridge.arms p z (d 2) (d 3)) j ≤ 9 := by
    by_cases hnine : 9 ≤ contacts G (JointBridge.arms p z (d 2) (d 3)) j
    · exact (h.common_triple hc hcard hdeg hn hj hjs hjd hnine).1.le
    · omega
  have hdis : Disjoint (p.support ∪ s ∪ d.support) j :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨h.paw_disjoint hj, c.property.blocks_disjoint h.first hj hjs.symm⟩,
      c.property.blocks_disjoint h.core hj hjd.symm⟩
  have hin : contacts G (JointBridge.arms p z (d 2) (d 3))
      (p.support ∪ s ∪ d.support ∪ j) ≤ 31 := by
    rw [contacts_union_right G _ hdis]
    omega
  have hsel : ({s, d.support, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (insert_subset h.core (singleton_subset_iff.mpr hj))
  have hthree : ({s, d.support, j} : Finset (Finset V)).card = 3 :=
    card_triple_eq_three_iff.mpr ⟨h.different.symm, hjs.symm, hjd.symm⟩
  have he : c.remainder ∪ ({s, d.support, j} : Finset (Finset V)).biUnion id =
      p.support ∪ s ∪ d.support ∪ j := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← h.paw, union_assoc]
  obtain ⟨b, hb, hbn, hh⟩ := JointFinal.exists_nine_outside_three31 hcard hdeg
    {s, d.support, j} hsel hthree (JointBridge.arms p z (d 2) (d 3)) h.arms_card (he.symm ▸ hin)
  simp only [mem_insert, mem_singleton, not_or] at hbn
  exact ⟨b, hb, hbn.1, hbn.2.1, hbn.2.2, hh⟩

end Erdos577.DenseObstruction

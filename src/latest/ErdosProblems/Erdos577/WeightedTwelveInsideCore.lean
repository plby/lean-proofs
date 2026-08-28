import ErdosProblems.Erdos577.WeightedTwelveConfiguration

/-! The exact four-row set has inside bound20 and forces a second outside heavy block. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Configuration.inside_twenty {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d) :
    contacts G (JointFinal.arms p q d) (p.support ∪ q.support ∪ d.support) ≤ 20 := by
  have hFQ := h.paw_disjoint h.first
  have hFA := h.pair.disjoint
  have hQA : Disjoint q.support d.support :=
    c.property.blocks_disjoint h.first h.core h.different.symm
  have hfull := disjoint_union_left.mpr ⟨hFA, hQA⟩
  have hxF : degreeIn G p.leaf p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G p.leaf p.leaf p.leaf_not_mem_triangle,
      if_neg G.irrefl, zero_add]
    exact p.leaf_triangle_degree_eq_one (by rw [h.paw]; exact c.no_quad_remainder hcard hn)
  have hx : degreeIn G p.leaf (p.support ∪ q.support ∪ d.support) = 4 := by
    rw [degreeIn_union G p.leaf hfull, degreeIn_union G p.leaf hFQ, hxF,
      (counts p q h.pattern).1, h.leaf_zero]
  have hym : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have hyT := JointClaims.triangle_column_le_one hc hcard hn p h.paw h.first
    (by rw [(counts p q h.pattern).1]) (q 3) hym
  have hyX : ¬G.Adj (q 3) p.leaf := fun hh ↦
    (by decide : ¬(7 : ℕ).testBit 3 = true) ((h.pattern.2.1 3).mp hh.symm)
  have hyF : degreeIn G (q 3) p.support ≤ 1 := by
    rw [p.support_eq, degreeIn_insert G (q 3) p.leaf p.leaf_not_mem_triangle,
      if_neg hyX, zero_add]
    exact hyT
  have hyQ : degreeIn G (q 3) q.support = 3 := by
    rw [q.degreeIn_eq]
    change 2 + (if G.Adj (q 3) (q 1) then 1 else 0) = 3
    rw [if_pos h.pattern.1.symm]
  have hy : degreeIn G (q 3) (p.support ∪ q.support ∪ d.support) ≤ 4 := by
    rw [degreeIn_union G (q 3) hfull, degreeIn_union G (q 3) hFQ,
      hyQ, h.cross_zero (q 3) hym]
    omega
  have hdrow (i : Fin 4) : degreeIn G (d i) (p.support ∪ q.support ∪ d.support) ≤ 6 := by
    apply JointCore.core_inside_bound p q d.card_support hFQ hFA hQA h.leaf_zero (d i)
      ((d.mem_support _).mpr ⟨i, rfl⟩)
    apply (degreeIn_eq_zero_iff (G := G) _ _).mpr
    intro u hu hadj
    exact (degreeIn_eq_zero_iff (G := G) _ _).mp (h.cross_zero u hu) (d i)
      ((d.mem_support _).mpr ⟨i, rfl⟩) hadj.symm
  rw [h.arms_contacts]
  have h2 := hdrow 2
  have h3 := hdrow 3
  omega

theorem Configuration.exists_second_heavy {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} (h : Configuration c p q d) :
    ∃ j ∈ c.blocks, j ≠ q.support ∧ j ≠ d.support ∧
      9 ≤ contacts G (JointFinal.arms p q d) j := by
  have hsel : ({q.support, d.support} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset h.first (singleton_subset_iff.mpr h.core)
  have he : c.remainder ∪ ({q.support, d.support} : Finset (Finset V)).biUnion id =
      p.support ∪ q.support ∪ d.support := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, ← h.paw, union_assoc]
  have hinside := h.inside_twenty hc hcard hn
  obtain ⟨j, hj, hjn, hnine⟩ := JointFirst.exists_nine_outside_two hcard hdeg
    {q.support, d.support} hsel (card_pair_eq_two_iff.mpr h.different.symm)
    (JointFinal.arms p q d) h.arms_card (by rw [he]; omega)
  simp only [mem_insert, mem_singleton, not_or] at hjn
  exact ⟨j, hj, hjn.1, hjn.2, hnine⟩

end Erdos577.WeightedTwelve

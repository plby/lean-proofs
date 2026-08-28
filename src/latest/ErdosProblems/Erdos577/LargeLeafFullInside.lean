import ErdosProblems.Erdos577.LargeLeafFullContact

/-! The full-leaf case supplies the two inside estimates required by the dense-pair obstruction. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_pair_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V}
    (h : DenseObstruction.PairConfig c p d s z)
    (hfull : degreeIn G p.leaf s = 4) (hb : degreeIn G (p.vertices 2) s = 2) :
    contacts G (JointBridge.arms p z (d 2) (d 3)) (p.support ∪ s ∪ d.support) ≤ 22 := by
  have hFS := h.paw_disjoint h.first
  have hFA := h.pair.disjoint
  have hSA : Disjoint s d.support := c.property.blocks_disjoint h.first h.core h.different.symm
  have hdis : Disjoint (p.support ∪ s) d.support := disjoint_union_left.mpr ⟨hFA, hSA⟩
  have hxzero := h.leaf_zero hcard hn
  obtain ⟨q, hq⟩ := c.property.blocks_quad s h.first
  have hx := JointCore.leaf_inside_bound p q (by rwa [hq]) hFA (by rwa [hq])
    (by rw [h.paw]; exact c.no_quad_remainder hcard hn) hxzero
  rw [hq] at hx
  have hzcore := (dense_core_bounds hc hcard hn p h.paw h.first (by omega) h.core
    h.different h.pair.dense).2.2 z h.exposed
  rw [degreeIn_union G z (hFA.mono_left (p.support_eq ▸ subset_insert _ _))] at hzcore
  have hclS := FullRow.full_leaf_clique hc p h.paw h.first hfull
  have hzS : degreeIn G z s = 3 := by
    rw [degreeIn_clique G hclS.isClique h.exposed, hclS.card_eq]
  have hz : degreeIn G z (p.support ∪ s ∪ d.support) ≤ 5 := by
    rw [degreeIn_union G z hdis, degreeIn_union G z hFS, p.support_eq,
      degreeIn_insert G z p.leaf p.leaf_not_mem_triangle, hzS]
    split_ifs <;> omega
  have hdrow (i : Fin 4) (hi : i = 2 ∨ i = 3) :
      degreeIn G (d i) (p.support ∪ s ∪ d.support) ≤ 6 := by
    have hr : G.Adj p.center (d i) := by
      rcases hi with rfl | rfl
      · exact h.pair.center_first
      · exact h.pair.center_second
    have hzero := full_two_core_neighbor_zero hc hcard hn p h.paw h.first hfull hb h.core
      h.different h.pair.dense (d i) ((d.mem_support _).mpr ⟨i, rfl⟩) hr
    have hh := JointCore.core_inside_bound p q d.card_support (by rwa [hq]) hFA
      (by rwa [hq]) hxzero (d i) ((d.mem_support _).mpr ⟨i, rfl⟩) (by rwa [hq])
    rwa [hq] at hh
  have h2 := hdrow 2 (Or.inl rfl)
  have h3 := hdrow 3 (Or.inr rfl)
  rw [h.arms_contacts]
  omega

end Erdos577.LargeLeaf

import ErdosProblems.Erdos577.LargeLeafFullPreparation

/-! Three noncentral contacts leave at most one first-block--core edge and give inside22. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma core_inside_with_row (p : Paw G) (q : Quadrilateral G) {a : Finset V} (ha : a.card = 4)
    (hFQ : Disjoint p.support q.support) (hFA : Disjoint p.support a)
    (hQA : Disjoint q.support a) (hx : degreeIn G p.leaf a = 0) (v : V) (hv : v ∈ a) :
    degreeIn G v (p.support ∪ q.support ∪ a) ≤ 6 + degreeIn G v q.support := by
  have hT : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hKQ : Disjoint (p.triangle ∪ a) q.support :=
    disjoint_union_left.mpr ⟨hFQ.mono_left hT, hQA.symm⟩
  have hKcard : (p.triangle ∪ a).card = 7 := by
    rw [card_union_of_disjoint (hFA.mono_left hT), p.triangle_clique.card_eq, ha]
  have hvK : v ∈ p.triangle ∪ a := mem_union_right _ hv
  have hK := degreeIn_le_card G v ((p.triangle ∪ a).erase v)
  rw [degreeIn_erase_self G v hvK, card_erase_of_mem hvK, hKcard] at hK
  have hxF : p.leaf ∈ p.support := p.support_eq ▸ mem_insert_self _ _
  have hxout : p.leaf ∉ (p.triangle ∪ a) ∪ q.support := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · rcases mem_union.mp hh with hh | hh
      · exact p.leaf_not_mem_triangle hh
      · exact disjoint_left.mp hFA hxF hh
    · exact disjoint_left.mp hFQ hxF hh
  have hvx : ¬G.Adj v p.leaf := fun hh ↦
    (degreeIn_eq_zero_iff (G := G) _ _).mp hx v hv hh.symm
  have he : p.support ∪ q.support ∪ a = insert p.leaf ((p.triangle ∪ a) ∪ q.support) := by
    rw [p.support_eq, insert_union, insert_union, union_right_comm]
  rw [he, degreeIn_insert G v p.leaf hxout, if_neg hvx, zero_add,
    degreeIn_union G v hKQ]
  omega

variable [Fintype V]

theorem three_cross_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hlarge : 3 ≤ degreeIn G p.leaf s)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s) (hT : 11 ≤ contacts G p.triangle a) :
    contacts G a s ≤ 1 := by
  have hbound := (dense_core_bounds hc hcard hn p hp hs hlarge ha has hT).2.2
  have hsum : contacts G s (p.triangle ∪ a) ≤ 4 := by
    calc
      _ ≤ ∑ _ ∈ s, 1 := sum_le_sum hbound
      _ = 4 := by simp [(c.property.blocks_quad s hs).card]
  have hTA : Disjoint p.triangle a := (c.presentPaw p hp).triangle_disjoint_block ha
  rw [contacts_union_right G s hTA, contacts_comm G s p.triangle, contacts_comm G s a] at hsum
  have htriangle := p.contacts_triangle s
  change contacts G p.triangle s = degreeIn G p.center s +
    (degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) at htriangle
  omega

theorem three_pair_inside {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V}
    (h : DenseObstruction.PairConfig c p d s z) (hthree : degreeIn G p.leaf s = 3)
    (hnon : 3 ≤ degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s) :
    contacts G (JointBridge.arms p z (d 2) (d 3)) (p.support ∪ s ∪ d.support) ≤ 22 := by
  have hFS := h.paw_disjoint h.first
  have hFA := h.pair.disjoint
  have hSA : Disjoint s d.support := c.property.blocks_disjoint h.first h.core h.different.symm
  have hxzero := h.leaf_zero hcard hn
  have hcore := (dense_core_bounds hc hcard hn p h.paw h.first (by omega) h.core
    h.different h.pair.dense).2.2
  obtain ⟨q, hq⟩ := c.property.blocks_quad s h.first
  have hz := JointFirst.inside_of_first_column p q (by rwa [hq]) hFA
    (by rw [hq]; exact hSA.symm) z
    (hq.symm ▸ h.exposed) (hcore z h.exposed)
  rw [hq] at hz
  have hxF : degreeIn G p.leaf p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G p.leaf p.leaf p.leaf_not_mem_triangle,
      if_neg G.irrefl, zero_add]
    exact p.leaf_triangle_degree_eq_one (by rw [h.paw]; exact c.no_quad_remainder hcard hn)
  have hx : degreeIn G p.leaf (p.support ∪ s ∪ d.support) = 4 := by
    rw [degreeIn_union G p.leaf (disjoint_union_left.mpr ⟨hFA, hSA⟩),
      degreeIn_union G p.leaf hFS, hxF, hthree, hxzero]
  have hdrow (i : Fin 4) : degreeIn G (d i) (p.support ∪ s ∪ d.support) ≤
      6 + degreeIn G (d i) s := by
    have hh := core_inside_with_row p q d.card_support (by rwa [hq]) hFA (by rwa [hq])
      hxzero (d i) ((d.mem_support _).mpr ⟨i, rfl⟩)
    rwa [hq] at hh
  have hcross := three_cross_le_one hc hcard hn p h.paw h.first (by omega) hnon
    h.core h.different h.pair.dense
  have hsub : ({d 2, d 3} : Finset V) ⊆ d.support :=
    insert_subset ((d.mem_support _).mpr ⟨2, rfl⟩)
      (singleton_subset_iff.mpr ((d.mem_support _).mpr ⟨3, rfl⟩))
  have hsum := sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ ↦ Nat.zero_le (degreeIn G v s))
  have h23 : d 2 ≠ d 3 := d.injective.ne (by decide)
  rw [sum_insert (by simpa only [mem_singleton] using h23), sum_singleton] at hsum
  change degreeIn G (d 2) s + degreeIn G (d 3) s ≤ contacts G d.support s at hsum
  have h2 := hdrow 2
  have h3 := hdrow 3
  rw [h.arms_contacts]
  omega

end Erdos577.LargeLeaf

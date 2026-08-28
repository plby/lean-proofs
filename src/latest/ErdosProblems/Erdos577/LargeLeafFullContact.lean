import ErdosProblems.Erdos577.LargeLeafFullCounts

/-! Every center neighbor in the dense block avoids the full-leaf first block. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem full_two_core_neighbor_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hfull : degreeIn G p.leaf s = 4) (hb : degreeIn G (p.vertices 2) s = 2)
    {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hT : 11 ≤ contacts G p.triangle a) (v : V) (hv : v ∈ a) (hrv : G.Adj p.center v) :
    degreeIn G v s = 0 := by
  obtain ⟨hclA, _, hcore⟩ := dense_core_bounds hc hcard hn p hp hs (by omega) ha has hT
  have hclS := FullRow.full_leaf_clique hc p hp hs hfull
  have hFS : Disjoint p.support s := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hAS : Disjoint a s := c.property.blocks_disjoint ha hs has
  have hm (i : Fin 4) : p.vertices i ∈ p.support := (mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩
  have hcross (i : Fin 4) : p.vertices i ≠ v := fun he ↦ disjoint_left.mp hFA (hm i) (he.symm ▸ hv)
  have hbx : p.vertices 2 ≠ p.leaf := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hbr : p.vertices 2 ≠ p.center := p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 1)
  have hTA := hFA.mono_left (p.support_eq ▸ subset_insert _ _)
  rw [degreeIn, card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu, hvu⟩ := mem_filter.mp hu
  by_cases hbu : G.Adj (p.vertices 2) u
  · have hsub : ({p.vertices 2, v} : Finset V) ⊆ (p.triangle ∪ a).filter (G.Adj u) :=
      insert_subset (mem_filter.mpr ⟨mem_union_left _ (by simp [Paw.triangle]), hbu.symm⟩)
        (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_union_right _ hv, hvu.symm⟩))
    have hcount := card_le_card hsub
    rw [card_pair (hcross 2)] at hcount
    have hbound := hcore u hu
    change 2 ≤ degreeIn G u (p.triangle ∪ a) at hcount
    omega
  · have hbout : p.vertices 2 ∉ s := fun hh ↦ disjoint_left.mp hFS (hm 2) hh
    have hbE : degreeIn G (p.vertices 2) (s.erase u) = 2 := by
      have hh := degreeIn_erase_add G (p.vertices 2) u hu
      rw [if_neg hbu, hb] at hh
      omega
    have hrep := (clique_replace_iff_two_contacts hclS hbout hu).mpr hbE.ge
    have hbase : Disjoint ({v, p.center, p.leaf} : Finset V) s :=
      disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hAS hv hh,
        disjoint_insert_left.mpr ⟨fun hh ↦ disjoint_left.mp hFS (hm 1) hh,
          disjoint_singleton_left.mpr (fun hh ↦ disjoint_left.mp hFS (hm 0) hh)⟩⟩
    have hboutside : p.vertices 2 ∉ ({v, p.center, p.leaf} : Finset V) ∪ s := by
      simp only [mem_union, mem_insert, mem_singleton, not_or]
      exact ⟨⟨hcross 2, hbr, hbx⟩, hbout⟩
    have hxu : G.Adj p.leaf u := (degreeIn_eq_card_iff p.leaf s).mp
      (hfull.trans hclS.card_eq.symm) u hu
    have hquad : QuadOn G {u, v, p.center, p.leaf} := QuadOn.of_vertices
      (fun he ↦ disjoint_left.mp hFS (show p.center ∈ p.support from hm 1) (he ▸ hu))
      (hcross 0).symm
      hvu.symm hrv.symm p.pendant.symm hxu
    have hf := LocalFactor.of_replacement hbase hboutside hu hquad hrep
    have he : insert (p.vertices 2) (({v, p.center, p.leaf} : Finset V) ∪ s) =
        insert p.leaf ({v, p.center, p.vertices 2} ∪ s) := by
      simp only [insert_union, singleton_union]
      rw [insert_comm p.center p.leaf, insert_comm v p.leaf,
        insert_comm (p.vertices 2) p.leaf, insert_comm (p.vertices 2) v,
        insert_comm (p.vertices 2) p.center]
    have huCore : ({v, p.center, p.vertices 2} : Finset V) ⊆ p.triangle ∪ a :=
      insert_subset (mem_union_right _ hv) (insert_subset (mem_union_left _ p.center_mem_triangle)
        (singleton_subset_iff.mpr (mem_union_left _ (by simp [Paw.triangle]))))
    have hrem := JointCore.dense_complement_triple p.triangle_clique hclA hTA hT
      v p.center (p.vertices 2) (mem_union_right _ hv) (mem_union_left _ p.center_mem_triangle)
      (mem_union_left _ (by simp [Paw.triangle])) (hcross 1).symm (hcross 2).symm hbr.symm
    exact hn (JointCore.hasPacking_of_partial_core hcard p hp ha hs has huCore hrem
      (he ▸ hf.partition))

end Erdos577.LargeLeaf

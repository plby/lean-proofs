import ErdosProblems.Erdos577.JointLossFactor

/-! Exact selected-block geometry for a triangle and a denser quadrilateral on seven vertices. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma pair_region_disjoint (c : TriangleChain G) (d : Quadrilateral G)
    (hd : d.support ∈ c.blocks) {j : Finset V} (hj : j ∈ c.blocks) (hdj : d.support ≠ j) :
    Disjoint (insert (d 0) c.triangle) (insert c.terminal ({d 2, d 3} ∪ j)) := by
  have hFd := c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hd)
  have hFj := c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hdJ : Disjoint d.support j := c.property.blocks_disjoint hd hj hdj
  have hm (i : Fin 4) : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have htri : c.triangle ⊆ c.remainder := subset_insert _ _
  have hd0out : d 0 ∉ insert c.terminal ({d 2, d 3} ∪ j) := by
    simp only [mem_insert, mem_union, mem_singleton, not_or]
    exact ⟨fun he ↦ c.terminal_not_mem_block hd (he ▸ hm 0),
      ⟨d.injective.ne (by decide), d.injective.ne (by decide)⟩,
      fun hh ↦ disjoint_left.mp hdJ (hm 0) hh⟩
  refine disjoint_insert_left.mpr ⟨hd0out, disjoint_insert_right.mpr
    ⟨c.property.terminal_not_mem, ?_⟩⟩
  refine disjoint_union_right.mpr ⟨?_, hFj.mono_left htri⟩
  exact (hFd.mono_left htri).mono_right
    (insert_subset (hm 2) (singleton_subset_iff.mpr (hm 3)))

omit [DecidableRel G.Adj] in
lemma pair_triangle_geometry (c : TriangleChain G) (d : Quadrilateral G)
    (hd : d.support ∈ c.blocks) {j : Finset V} (hj : j ∈ c.blocks) (hdj : d.support ≠ j)
    (haux : G.IsNClique 4 (insert (d 0) c.triangle))
    {t b : Finset V} (ht : G.IsNClique 3 t) (hb : QuadOn G b) (htb : Disjoint t b)
    (hcover : t ∪ b = insert c.terminal ({d 2, d 3} ∪ j)) :
    Disjoint (insert (d 0) c.triangle) b ∧
      (insert (d 0) c.triangle) ∪ b ⊆ c.remainder ∪ (d.support ∪ j) ∧
      ((c.remainder ∪ (d.support ∪ j)) \ ((insert (d 0) c.triangle) ∪ b)).card = 4 ∧
      TriangleIn G ((c.remainder ∪ (d.support ∪ j)) \ ((insert (d 0) c.triangle) ∪ b)) := by
  have hFd := c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hd)
  have hFj := c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hj)
  have hdJ : Disjoint d.support j := c.property.blocks_disjoint hd hj hdj
  have hm (i : Fin 4) : d i ∈ d.support := (d.mem_support _).mpr ⟨i, rfl⟩
  have htri : c.triangle ⊆ c.remainder := subset_insert _ _
  have hsub : insert c.terminal ({d 2, d 3} ∪ j) ⊆ c.remainder ∪ (d.support ∪ j) := by
    refine insert_subset (mem_union_left _ (mem_insert_self _ _)) (union_subset ?_ ?_)
    · exact insert_subset (mem_union_right _ (mem_union_left _ (hm 2)))
        (singleton_subset_iff.mpr (mem_union_right _ (mem_union_left _ (hm 3))))
    · exact fun _ hh ↦ mem_union_right _ (mem_union_right _ hh)
  have hasub : insert (d 0) c.triangle ⊆ c.remainder ∪ (d.support ∪ j) :=
    insert_subset (mem_union_right _ (mem_union_left _ (hm 0)))
      (fun _ hh ↦ mem_union_left _ (htri hh))
  have htS : t ⊆ insert c.terminal ({d 2, d 3} ∪ j) := hcover ▸ subset_union_left
  have hbS : b ⊆ insert c.terminal ({d 2, d 3} ∪ j) := hcover ▸ subset_union_right
  have had := pair_region_disjoint c d hd hj hdj
  have hab := had.mono_right hbS
  have habsub := union_subset hasub (hbS.trans hsub)
  have hcard : ((c.remainder ∪ (d.support ∪ j)) \ ((insert (d 0) c.triangle) ∪ b)).card = 4 := by
    rw [card_sdiff_of_subset habsub,
      card_union_of_disjoint (disjoint_union_right.mpr ⟨hFd, hFj⟩),
      card_union_of_disjoint hdJ, card_union_of_disjoint hab, c.card_remainder,
      d.card_support, (c.property.blocks_quad j hj).card, haux.card_eq, hb.card]
  refine ⟨hab, habsub, hcard, t, ?_, ht⟩
  have htout : Disjoint t ((insert (d 0) c.triangle) ∪ b) :=
    disjoint_union_right.mpr ⟨(had.mono_right htS).symm, htb⟩
  intro u hu
  exact mem_sdiff.mpr ⟨hsub (htS hu), fun hh ↦ disjoint_left.mp htout hu hh⟩

theorem pair_triangle_edges_le {c : TriangleChain G} (hc : c.Feasible)
    (d : Quadrilateral G) (hd : d.support ∈ c.blocks)
    {j : Finset V} (hj : j ∈ c.blocks) (hdj : d.support ≠ j)
    (hA : edgeCount G d.support = 6)
    (haux : G.IsNClique 4 (insert (d 0) c.triangle))
    {t b : Finset V} (ht : G.IsNClique 3 t) (hb : QuadOn G b) (htb : Disjoint t b)
    (hcover : t ∪ b = insert c.terminal ({d 2, d 3} ∪ j)) :
    edgeCount G b ≤ edgeCount G j := by
  obtain ⟨hab, hsub, hcard, htri⟩ := pair_triangle_geometry c d hd hj hdj haux ht hb htb hcover
  let parts := (BlockPartition.single (QuadOn.of_clique haux.card_eq haux.isClique)).union
    (BlockPartition.single hb) hab
  have hsel : ({d.support, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hd (singleton_subset_iff.mpr hj)
  have hcore : c.remainder ∪ ({d.support, j} : Finset (Finset V)).biUnion id =
      c.remainder ∪ (d.support ∪ j) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq]
  have hbound := hc.selected_edges_le {d.support, j} hsel parts
    (by rwa [hcore]) (by rwa [hcore]) (by rwa [hcore])
  have hold : (c.complementPartition.select {d.support, j} hsel).weightSum (edgeCount G) =
      edgeCount G d.support + edgeCount G j := by
    change ∑ s ∈ ({d.support, j} : Finset (Finset V)), edgeCount G s = _
    exact sum_pair hdj
  have he : edgeCount G (insert (d 0) c.triangle) = 6 := by
    rw [edgeCount_clique haux.isClique, haux.card_eq]
    rfl
  rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
    BlockPartition.weightSum_single, hold, hA, he] at hbound
  omega

end Erdos577.JointFinal
